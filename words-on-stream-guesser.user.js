// ==UserScript==
// @name         Words on Stream — Auto Guesser (Local LLM)
// @namespace    http://tampermonkey.net/
// @version      4.30
// @updateURL    https://raw.githubusercontent.com/cobrahjh/wos-data/main/words-on-stream-guesser.user.js
// @downloadURL  https://raw.githubusercontent.com/cobrahjh/wos-data/main/words-on-stream-guesser.user.js
// @description  Twitch tab: scans video + auto-types chat. wos.gg tab: reads tiles from DOM, pre-generates words, hands them to the Twitch tab via GM shared storage. Dict-backed anagram solver (ENABLE1, public domain); text LLM removed; vision LLM kept for Twitch tile reading.
// @author       Claude
// @match        https://www.twitch.tv/*
// @match        https://wos.gg/r/*
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_addValueChangeListener
// @grant        GM_xmlhttpRequest
// @connect      localhost
// @connect      127.0.0.1
// @connect      raw.githubusercontent.com
// ==/UserScript==

(function () {
  'use strict';

  // ── Config ────────────────────────────────────────────────────────────────
  let ollamaBase    = GM_getValue('ollama_base',    'http://localhost:11434');
  let visionModel   = GM_getValue('vision_model',   'llava');
  // When true, scan goes through claude-relay's /scan-image endpoint
  // (subscription CLI, $0 marginal, ~15-35s/scan, very accurate). When false,
  // scan uses the local Ollama vision model (faster, less accurate).
  let useClaude     = GM_getValue('use_claude_vision', false);
  // ENABLE1 — public-domain ~173k-word list. Avoids TWL06 (Hasbro-owned).
  let dictUrl       = GM_getValue('dict_url',       'https://raw.githubusercontent.com/dolph/dictionary/master/enable1.txt');
  // Grade filter: 'all' disables it; otherwise 0 (K) … 12 keeps only words at or
  // below that US school grade (cumulative — easier words included). A word's
  // grade comes from the AoA dataset (grade-words.tsv); words not in it fall back
  // to a frequency-rank-derived grade, so there are no coverage gaps. If the
  // grade list never loads, every word uses the frequency proxy.
  let gradeLevel = GM_getValue('grade_level', 'all'); // 'all' | 0..12
  // Normalise a legacy/stringified/out-of-range stored value so the numeric
  // `<= gradeLevel` comparison is always number≤number (or cleanly bypassed).
  if (gradeLevel !== 'all') {
    gradeLevel = parseInt(gradeLevel, 10);
    if (!(gradeLevel >= 0 && gradeLevel <= 12)) gradeLevel = 'all';
  }

  // Dictionary state — populated lazily by ensureDict(), shared across both
  // host modes. Two structures share one index pass: Set for O(1) word
  // validation, Map<sortedLetters, word[]> for anagram lookup.
  // All dict state (incl. DICT_CACHE_KEY and dictLoading) is hoisted up here
  // because Twitch-branch handlers and the wos.gg tick() reference these
  // names before their original declaration sites would have run — TDZ
  // otherwise, and the failures are silent inside async functions.
  const DICT_CACHE_KEY = 'wos_dict_v1';
  let dictSet     = null;
  let dictByKey   = null;
  let freqRank    = null; // Map<word, rank>. Lower rank = more common.
  let dictLoading = null;
  // Bumped whenever a newer dict load (file pick / refresh / URL change) should
  // supersede an in-flight network fetch — fetchDict checks this in onload so a
  // slow or failed fetch can't overwrite a dict the user just loaded another way.
  let dictGen     = 0;

  // Grade-level data (AoA-derived word→grade). Loaded lazily, GM-cached, parallel
  // to the dict. gradeMap: Map<WORD, 0..12>. Hosted in the PUBLIC cobrahjh/wos-data
  // repo — DevClaude is private and raw.githubusercontent 404s unauthenticated on
  // private repos; raw.githubusercontent is already in @connect (no manifest change).
  const GRADE_CACHE_KEY = 'wos_grades_v1';
  let gradeMap     = null;
  let gradeLoading = null;
  let gradeGen     = 0;
  let gradeUrl     = GM_getValue('grade_url', 'https://raw.githubusercontent.com/cobrahjh/wos-data/main/grade-words.tsv');

  // ── Host routing ──────────────────────────────────────────────────────────
  // wos.gg is the game's own companion page: tiles are in the DOM, no vision
  // needed. Twitch is the chat-send side. Both pages share round state via
  // GM_setValue under key 'wos_round_state'.
  if (location.hostname.endsWith('wos.gg')) {
    runWosGgMode();
    return;
  }

  // ── State (twitch.tv branch) ──────────────────────────────────────────────
  let detectedLetters = [];   // all letters from scan
  let fakeLetters     = [];   // letters marked fake
  // Suggested words shown as clickable chips. Each entry tracks sent state so
  // the chip can fade/strikethrough after the user clicks it.
  let wordList        = []; // [{ word: string, sent: boolean }] — current filtered view
  let allWords        = []; // full cleaned word set from the last gen/pull (pre-filter source)
  let scanning        = false; // re-entry guard for the Scan button
  let sendingAll      = false; // Send-all run in progress
  let sendAllTimer    = null;

  // ── Untrusted-data validation ─────────────────────────────────────────────
  // LLM scan output, scraped DOM, and GM cross-tab state are all untrusted and
  // must be reduced to plain A–Z before they reach the multiset solver or any
  // innerHTML sink. HTML/attribute-injection payloads collapse to '' and get
  // dropped by the length filters downstream.
  function cleanLetters(arr) {
    return (Array.isArray(arr) ? arr : [])
      .flatMap(l => String(l).toUpperCase().replace(/[^A-Z]/g, '').split(''))
      .filter(Boolean);
  }
  function cleanWord(w) {
    return String(w).toUpperCase().replace(/[^A-Z]/g, '');
  }
  // wos_round_state can be written by any wos.gg/r/* page or a poisoned GM value.
  function isValidRoundState(s) {
    return !!s && Array.isArray(s.words) && typeof s.ts === 'number';
  }
  // Cross-tab round state older than this is ignored (Pull warns; auto-load
  // silently skips). One threshold (5 min) for both code paths.
  const STATE_STALE_MS = 5 * 60 * 1000;
  // Count of words not yet sent — used in status lines and the chip counter.
  const remainingCount = () => wordList.filter(w => !w.sent).length;

  // ── Inject UI ─────────────────────────────────────────────────────────────
  const panel = document.createElement('div');
  panel.id = 'wos-panel';
  panel.innerHTML = `
<style>
  #wos-panel {
    position:fixed; bottom:80px; right:16px; width:270px;
    max-height:calc(100vh - 120px); overflow-y:auto;
    background:#0f0a1e; border:2px solid #7c3aed; border-radius:12px;
    padding:12px; z-index:2147483647; font-family:'Segoe UI',sans-serif;
    color:#e9d5ff; box-shadow:0 0 28px rgba(168,85,247,.5);
  }
  /* Scrollbar styling so the panel doesn't look broken when overflow kicks in */
  #wos-panel::-webkit-scrollbar { width:8px; }
  #wos-panel::-webkit-scrollbar-thumb { background:#7c3aed; border-radius:4px; }
  #wos-panel::-webkit-scrollbar-track { background:rgba(168,85,247,.1); }
  #wos-panel h3 {
    margin:0 0 8px; font-size:.78rem; letter-spacing:3px;
    color:#c084fc; text-transform:uppercase; text-align:center;
  }
  #wos-panel .section {
    background:rgba(109,40,217,.12); border:1px solid rgba(168,85,247,.22);
    border-radius:8px; padding:8px; margin-bottom:8px;
  }
  #wos-panel .section-title {
    font-size:.6rem; letter-spacing:2px; color:#a78bfa;
    text-transform:uppercase; margin-bottom:6px;
  }
  #wos-panel input[type=text],
  #wos-panel input[type=number] {
    width:100%; background:rgba(109,40,217,.2);
    border:1px solid rgba(168,85,247,.35); border-radius:5px;
    color:#e9d5ff; font-size:.78rem; padding:5px 7px;
    outline:none; box-sizing:border-box;
  }
  #wos-panel textarea {
    width:100%; height:75px; background:rgba(109,40,217,.2);
    border:1px solid rgba(168,85,247,.35); border-radius:5px;
    color:#e9d5ff; font-size:.82rem; padding:6px; resize:none;
    outline:none; box-sizing:border-box;
    text-transform:uppercase; letter-spacing:1px;
  }
  #wos-panel .row { display:flex; gap:6px; margin-top:5px; align-items:center; }
  #wos-panel label { font-size:.6rem; color:#a78bfa; letter-spacing:1px;
    text-transform:uppercase; white-space:nowrap; }
  #wos-panel button {
    flex:1; padding:7px 0; border:none; border-radius:7px;
    font-size:.72rem; font-weight:700; letter-spacing:1px;
    text-transform:uppercase; cursor:pointer; transition:opacity .15s;
  }
  .btn-scan  { background:linear-gradient(180deg,#06b6d4,#0e7490); color:#fff; box-shadow:0 3px 0 #164e63; }
  .btn-start { background:linear-gradient(180deg,#a855f7,#7c3aed); color:#fff; box-shadow:0 3px 0 #3b0764; }
  .btn-stop  { background:linear-gradient(180deg,#dc2626,#991b1b); color:#fff; box-shadow:0 3px 0 #7f1d1d; }
  .btn-ghost { background:rgba(168,85,247,.13); color:#c084fc;
    border:1px solid rgba(168,85,247,.28) !important; box-shadow:none; }
  button:disabled { opacity:.35; cursor:not-allowed; }

  /* Letter chips */
  #wos-letters-wrap {
    display:flex; flex-wrap:wrap; gap:4px;
    justify-content:center; min-height:36px; margin:4px 0 2px;
  }
  /* Clickable word chips — click to send into Twitch chat. Sent words fade
     and strikethrough so the remaining set is obvious. */
  #wos-words-list {
    display:block;
    min-height:40px;
    padding:4px; background:rgba(109,40,217,.12);
    border:1px solid rgba(168,85,247,.22); border-radius:5px;
  }
  /* Words grouped under grade headings (K, 1 … 12). */
  .wos-grade-group { display:flex; flex-wrap:wrap; gap:3px; align-items:center; margin-bottom:5px; }
  .wos-grade-label { flex:0 0 100%; font-size:.55rem; color:#a78bfa; letter-spacing:1px;
    text-transform:uppercase; margin:2px 0 1px; opacity:.8; }
  .wos-word-chip {
    padding:3px 7px; background:linear-gradient(180deg,#7c3aed,#5b21b6);
    border:1px solid #a855f7; border-radius:4px; color:#fff;
    font-size:.72rem; font-weight:700; letter-spacing:1px;
    text-transform:uppercase; cursor:pointer; user-select:none;
    transition:opacity .15s, transform .1s;
  }
  .wos-word-chip:hover { background:linear-gradient(180deg,#a855f7,#7c3aed); transform:translateY(-1px); }
  .wos-word-chip.sent {
    opacity:.3; text-decoration:line-through; cursor:default;
    background:rgba(109,40,217,.3); border-color:rgba(168,85,247,.3);
  }
  .wos-word-chip.sent:hover { transform:none; }
  /* A-Z picker buttons (click to add a letter to the scan chips) */
  #wos-letter-picker {
    display:none; flex-wrap:wrap; gap:2px;
    justify-content:center; margin-top:4px;
  }
  .wos-pick-letter {
    flex:0 0 auto; padding:3px 0; min-width:22px;
    background:rgba(124,58,237,.3); border:1px solid #7c3aed;
    border-radius:3px; color:#fff; font-size:.7rem; font-weight:700;
    cursor:pointer; box-shadow:none; user-select:none;
  }
  .wos-pick-letter:hover { background:#7c3aed; }
  .lchip {
    padding:5px 9px; border-radius:6px; font-weight:900;
    font-size:.9rem; letter-spacing:1px; cursor:pointer;
    user-select:none; transition:all .15s;
    background:linear-gradient(180deg,#7c3aed,#5b21b6);
    border:2px solid #a855f7; color:#fff; box-shadow:0 3px 0 #3b0764;
    position:relative;
  }
  .lchip.fake {
    background:linear-gradient(180deg,#dc2626,#991b1b) !important;
    border-color:#f87171 !important; box-shadow:0 3px 0 #7f1d1d !important;
  }
  .lchip .badge {
    position:absolute; top:-6px; right:-4px; background:#4b5563;
    color:#fff; border-radius:50%; width:14px; height:14px;
    font-size:.6rem; display:flex; align-items:center; justify-content:center;
    font-weight:900; line-height:1; cursor:pointer;
  }
  .lchip .badge:hover { background:#dc2626; transform:scale(1.15); }
  .lchip.fake .badge { background:#f87171; }
  .chip-hint { font-size:.62rem; color:#6d28d9; letter-spacing:1px; align-self:center; }

  #wos-fake-list {
    font-size:.68rem; color:#f87171; letter-spacing:1px;
    text-align:center; min-height:13px; margin-top:3px;
  }
  #wos-status   { margin-top:6px; font-size:.67rem; color:#a78bfa;
    letter-spacing:1px; text-align:center; min-height:13px; text-transform:uppercase; }
  #wos-progress { font-size:.67rem; color:#4ade80; text-align:center;
    letter-spacing:1px; min-height:13px; text-transform:uppercase; }

  #wos-toggle {
    position:fixed; bottom:40px; right:16px; background:#7c3aed;
    color:#fff; border:none; border-radius:50%; width:36px; height:36px;
    font-size:1rem; cursor:pointer; z-index:2147483647;
    box-shadow:0 0 14px rgba(168,85,247,.65);
  }
  /* Native <select> popup options inherit the panel's light text but render on a
     light system background → invisible. Force a readable dark option background. */
  #wos-grade-level { background:#1a1033 !important; color:#e9d5ff; }
  #wos-grade-level option { background:#1a1033; color:#e9d5ff; }
</style>

<h3>⚡ WoS · Local LLM</h3>
<div class="row"><button class="btn-ghost" id="wos-btn-help" style="flex:1;padding:4px 0;font-size:.62rem;">❓ How to use</button></div>

<!-- Scan + letters -->
<div class="section">
  <div class="section-title">1 · Scan Stream — tap chips to toggle fake</div>
  <div id="wos-letters-wrap"><span class="chip-hint">No scan yet</span></div>
  <div id="wos-fake-list"></div>
  <div class="row">
    <button class="btn-scan" id="wos-btn-scan">🔍 Scan Letters</button>
    <button class="btn-ghost" id="wos-btn-add-letter" style="flex:none;padding:7px 10px;font-size:.68rem;">+ Letter</button>
    <button class="btn-ghost" id="wos-btn-genwords" disabled style="flex:none;padding:7px 10px;font-size:.68rem;">⚡ Gen Words</button>
  </div>
  <div class="row">
    <label>Type</label>
    <input type="text" id="wos-letter-input" placeholder="type letters here…" autocomplete="off" spellcheck="false" style="flex:1;text-transform:uppercase;letter-spacing:2px;"/>
  </div>
  <div id="wos-letter-picker"></div>
  <div class="row">
    <button class="btn-ghost" id="wos-btn-pull"          style="flex:1;padding:5px 10px;font-size:.65rem;">📥 Pull from wos.gg tab</button>
    <button class="btn-ghost" id="wos-btn-clear-letters" style="flex:none;padding:5px 10px;font-size:.65rem;">✕ Letters</button>
  </div>
  <div class="row">
    <button class="btn-ghost" id="wos-btn-debug-frame" style="flex:1;padding:5px 10px;font-size:.62rem;">📷 Show last frame</button>
    <button class="btn-ghost" id="wos-btn-debug-raw"   style="flex:1;padding:5px 10px;font-size:.62rem;">📋 Show last AI output</button>
  </div>
</div>

<!-- Words -->
<div class="section">
  <div class="section-title">2 · Words <span id="wos-words-count" style="color:#fff;">(0)</span> — click to send</div>
  <div id="wos-words-list"></div>
  <div class="row">
    <button class="btn-start" id="wos-btn-sendall" style="flex:1;padding:6px 0;font-size:.7rem;">▶ Send all</button>
  </div>
  <div class="row">
    <label>Min len</label>
    <input type="number" id="wos-min-len" value="4" min="4" max="9" step="1" style="width:45px;"/>
    <button class="btn-ghost" id="wos-btn-clear" style="flex:none;padding:5px 10px;font-size:.65rem;">✕ Words</button>
  </div>
  <div class="row" style="font-size:.62rem;color:#c084fc;">
    <label style="flex:none;">Grade ≤</label>
    <select id="wos-grade-level" style="flex:1;background:rgba(109,40,217,.2);border:1px solid rgba(168,85,247,.35);border-radius:5px;color:#e9d5ff;font-size:.72rem;padding:4px 6px;outline:none;">
      <option value="all">All words</option>
      <option value="0">K</option>
      <option value="1">1</option><option value="2">2</option><option value="3">3</option>
      <option value="4">4</option><option value="5">5</option><option value="6">6</option>
      <option value="7">7</option><option value="8">8</option><option value="9">9</option>
      <option value="10">10</option><option value="11">11</option><option value="12">12</option>
    </select>
    <span id="wos-grade-status" style="flex:none;font-size:.58rem;color:#a78bfa;margin-left:4px;"></span>
  </div>
</div>

<!-- Ollama config (advanced — rarely touched, kept at the bottom) -->
<div class="section">
  <div class="section-title">Ollama Settings</div>
  <div class="row">
    <label>URL</label>
    <input type="text" id="wos-ollama-base"  placeholder="http://localhost:11434"/>
  </div>
  <div class="row">
    <label>Vision</label>
    <input type="text" id="wos-vision-model" placeholder="llava"/>
  </div>
  <div class="row" style="font-size:.62rem;color:#c084fc;">
    <label style="flex:none;cursor:pointer;">
      <input type="checkbox" id="wos-use-claude" style="vertical-align:middle;margin-right:5px;"/>
      Use Claude vision (slow, accurate)
    </label>
  </div>
  <div class="row">
    <label>Dict</label>
    <input type="text" id="wos-dict-url" placeholder="wordlist URL"/>
  </div>
  <div class="row">
    <button class="btn-ghost" id="wos-save-cfg"     style="flex:none;padding:5px 12px;font-size:.65rem;">💾 Save</button>
    <button class="btn-ghost" id="wos-refresh-dict" style="flex:none;padding:5px 12px;font-size:.65rem;">🔁 Dict</button>
    <span id="wos-cfg-status" style="font-size:.65rem;color:#4ade80;letter-spacing:1px;"></span>
  </div>
  <div class="row">
    <label style="flex:none;">Or load file</label>
    <input type="file" id="wos-dict-file" accept=".txt,text/plain" style="flex:1;color:#c084fc;font-size:.65rem;"/>
  </div>
  <div id="wos-dict-status" style="font-size:.62rem;color:#a78bfa;letter-spacing:1px;margin-top:4px;text-align:center;">📚 Dict not loaded</div>
</div>

<div id="wos-status" aria-live="polite">Ready — make sure Ollama is running</div>
`;

  const toggle = document.createElement('button');
  toggle.id = 'wos-toggle';
  toggle.textContent = '💬';
  document.body.appendChild(toggle);
  document.body.appendChild(panel);

  // Set config field values via property (not innerHTML interpolation) to
  // avoid HTML/attribute injection if a stored value contains quotes or tags.
  document.getElementById('wos-ollama-base').value  = ollamaBase;
  document.getElementById('wos-vision-model').value = visionModel;
  document.getElementById('wos-dict-url').value     = dictUrl;
  document.getElementById('wos-use-claude').checked = useClaude;
  document.getElementById('wos-grade-level').value = String(gradeLevel);
  // Persist grade selection and rebuild the list so suggestions reflect the
  // new filter immediately (preserveSent keeps any words you've already sent).
  document.getElementById('wos-grade-level').addEventListener('change', e => {
    gradeLevel = e.target.value === 'all' ? 'all' : parseInt(e.target.value, 10);
    GM_setValue('grade_level', gradeLevel);
    // Re-filter the full set (cumulative, non-destructive — raising the grade re-adds words).
    if (allWords.length) applyFilters(true);
  });
  // Min len also re-filters live from the full set.
  document.getElementById('wos-min-len').addEventListener('input', () => {
    if (allWords.length) applyFilters(true);
  });

  // ── Tooltips ───────────────────────────────────────────────────────────────
  // Hover help on each control, set in one place rather than 20 title= attrs.
  const TIPS = {
    'wos-btn-help': 'Open the full how-to guide in a new tab.',
    'wos-btn-scan': 'Capture the stream and read the letter tiles (first scan asks which window to share).',
    'wos-btn-add-letter': 'Add letters by hand with an A–Z picker.',
    'wos-btn-genwords': 'Generate every dictionary word makeable from the current letters.',
    'wos-letter-input': 'Type letters — each A–Z key becomes a tile; Backspace removes the last.',
    'wos-btn-pull': 'Pull the latest solved words from the wos.gg companion tab.',
    'wos-btn-clear-letters': 'Clear the scanned letters (suggestions stay).',
    'wos-btn-debug-frame': 'Open the last captured frame in a new tab (debug).',
    'wos-btn-debug-raw': 'Open the last raw AI output in a new tab (debug).',
    'wos-btn-sendall': 'Auto-send every unsent word ~1.7s apart; click again to stop.',
    'wos-btn-clear': 'Clear the suggestion list (letters stay).',
    'wos-min-len': 'Shortest word to show (floor 4 — WoS rejects 3-letter words).',
    'wos-grade-level': 'Show only words at or below this US school grade (cumulative — easier words included).',
    'wos-use-claude': 'Use Claude vision (slow ~15–35s, very accurate) instead of local Ollama.',
    'wos-ollama-base': 'Local Ollama server URL.',
    'wos-vision-model': 'Ollama vision model name (used when Claude vision is off).',
    'wos-dict-url': 'Wordlist URL (fetched once, cached). Must be on raw.githubusercontent.com.',
    'wos-dict-file': 'Load a wordlist from a local .txt file (no network).',
    'wos-save-cfg': 'Save these settings.',
    'wos-refresh-dict': 'Re-download the wordlist.',
  };
  for (const [id, t] of Object.entries(TIPS)) {
    const el = document.getElementById(id);
    if (el) el.title = t;
  }

  // ── Help doc ───────────────────────────────────────────────────────────────
  // Static literal (no untrusted data) → safe to assign as innerHTML.
  const HELP_HTML = `
    <div style="max-width:680px;margin:24px auto;padding:0 18px 40px;font-family:'Segoe UI',sans-serif;color:#e9d5ff;line-height:1.55;">
      <h1 style="color:#c084fc;">⚡ Words on Stream — Auto Guesser</h1>
      <p>Reads the letter tiles, solves the anagrams, and lets you send words into Twitch chat.</p>
      <h2 style="color:#a78bfa;">Quick start</h2>
      <p><b>Companion mode (easiest):</b> open the <b>wos.gg</b> room tab and the <b>twitch.tv</b> channel tab. The wos.gg tab solves each round and pushes words to Twitch automatically — or click <b>📥 Pull from wos.gg tab</b>. Then click a word to send it, or use <b>▶ Send all</b>.</p>
      <p><b>Vision mode (no companion tab):</b> on the Twitch tab click <b>🔍 Scan Letters</b>, pick the stream window to share, fix any misread letters (click a chip to mark it fake, click ✕ to remove), then <b>⚡ Gen Words</b>.</p>
      <h2 style="color:#a78bfa;">Sending words</h2>
      <ul>
        <li>Click a <b>word chip</b> to type and submit it — it greys out once sent.</li>
        <li><b>▶ Send all</b> auto-sends every unsent word ~1.7&nbsp;s apart (to stay under Twitch's chat rate-limit). <b>⏹ Stop</b> halts it; changing the word list or grade filter also stops it.</li>
      </ul>
      <h2 style="color:#a78bfa;">Filters</h2>
      <ul>
        <li><b>Min len</b> — shortest word to show (floor 4; WoS rejects 3-letter words).</li>
        <li><b>Grade ≤</b> — show only words at or below a chosen US school grade (cumulative, so "Grade 4" includes everything easier). The little chip shows <code>31,067w</code> when real grade data is loaded, or <code>freq</code> when it's falling back to a frequency estimate.</li>
      </ul>
      <h2 style="color:#a78bfa;">The panel</h2>
      <ul>
        <li>Drag the <b>title bar</b> to move it; <b>double-click</b> or <b>long-press</b> the title to reset its position.</li>
        <li>The <b>💬</b> button (bottom-right) hides / shows the panel.</li>
        <li><b>Use Claude vision</b> (Ollama Settings) reads tiles much more accurately than the local model, but each scan takes ~15–35&nbsp;s.</li>
        <li><b>🔁 Dict</b> re-downloads the wordlist; <b>Or load file</b> loads one from disk if the network is blocked.</li>
      </ul>
    </div>`;
  document.getElementById('wos-btn-help').addEventListener('click', () => {
    const w = window.open();
    if (!w) { setStatus('⚠ Pop-up blocked — allow pop-ups to see help', '#facc15'); return; }
    w.document.title = 'WoS Auto-Guesser — Help';
    w.document.body.style.cssText = 'margin:0;background:#0f0a1e';
    w.document.body.innerHTML = HELP_HTML;
  });

  // Build the A-Z letter picker once. Each button adds its letter to the
  // detected-letters chip row; the picker stays open so multiple letters can
  // be added without re-clicking + Letter.
  const picker = document.getElementById('wos-letter-picker');
  'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('').forEach(L => {
    const b = document.createElement('button');
    b.textContent = L;
    b.className = 'wos-pick-letter';
    b.dataset.letter = L;
    picker.appendChild(b);
  });
  document.getElementById('wos-btn-add-letter').addEventListener('click', () => {
    picker.style.display = picker.style.display === 'flex' ? 'none' : 'flex';
  });
  picker.addEventListener('click', e => {
    if (!e.target.classList.contains('wos-pick-letter')) return;
    detectedLetters.push(e.target.dataset.letter);
    renderLetters();
    document.getElementById('wos-btn-genwords').disabled = false;
  });

  // Keyboard letter input: each A–Z character typed becomes a chip, the field
  // self-clears after each input. Backspace in the empty field removes the
  // most-recently-added chip (and any fake marker on it). Type fast — chips
  // appear as you go without needing Enter.
  const letterInput = document.getElementById('wos-letter-input');
  letterInput.addEventListener('input', e => {
    const text = (e.target.value || '').toUpperCase().replace(/[^A-Z]/g, '');
    if (!text) { e.target.value = ''; return; }
    for (const L of text) detectedLetters.push(L);
    renderLetters();
    document.getElementById('wos-btn-genwords').disabled = false;
    e.target.value = '';
  });
  letterInput.addEventListener('keydown', e => {
    if (e.key === 'Backspace' && !e.target.value && detectedLetters.length > 0) {
      e.preventDefault();
      const removedIdx = detectedLetters.length - 1;
      detectedLetters.pop();
      fakeLetters = fakeLetters.filter(k => parseInt(k.split(':')[1], 10) !== removedIdx);
      renderLetters();
      if (detectedLetters.length === 0) {
        document.getElementById('wos-btn-genwords').disabled = true;
      }
    }
  });

  toggle.addEventListener('click', () => {
    panel.style.display = panel.style.display === 'none' ? 'block' : 'none';
  });

  // Drag the panel by its header (the "⚡ WoS · Local LLM" title bar). Uses
  // Pointer Events + setPointerCapture so the drag keeps tracking even when the
  // cursor crosses the Twitch player — an iframe/video otherwise swallows
  // mousemove and the panel "sticks" mid-drag. Position persists via GM storage.
  (function makeDraggable() {
    const handle = panel.querySelector('h3');
    if (!handle) return;
    handle.style.cursor = 'move';
    handle.style.userSelect = 'none';
    handle.style.touchAction = 'none'; // we own the drag gesture (also enables touch drag)
    handle.style.webkitTouchCallout = 'none'; // suppress iOS long-press callout (we use long-press for reset)
    // Grip affordance: a divider under the title makes the drag zone legible
    // without needing the hover tooltip (which touch users never see).
    handle.style.borderBottom = '1px solid rgba(168,85,247,0.35)';
    handle.style.paddingBottom = '6px';
    handle.title = 'Drag to move · double-click or long-press to reset';

    // Clamp so the drag handle (h3) is always reachable. Twitch's top nav +
    // player overlay extends down to ~100px, plus we reserve ~30px so the
    // entire header band stays visible (not just the top edge).
    const MIN_TOP = 120;
    function clamp(left, top) {
      // Ensure at least 200px of panel height remains visible at the bottom.
      const maxX = window.innerWidth  - 80;
      const maxY = window.innerHeight - 200;
      return {
        left: Math.max(0, Math.min(left, maxX)),
        top:  Math.max(MIN_TOP, Math.min(top, maxY)),
      };
    }

    const saved = GM_getValue('panel_pos', null);
    if (saved && saved.left && saved.top) {
      // Re-clamp on restore in case window shrunk since the save.
      const l = parseInt(saved.left, 10) || 0;
      const t = parseInt(saved.top,  10) || MIN_TOP;
      const c = clamp(l, t);
      panel.style.left = c.left + 'px';
      panel.style.top  = c.top  + 'px';
      panel.style.right  = 'auto';
      panel.style.bottom = 'auto';
    }

    let dragging = false;
    let activePointerId = null;
    let pressTimer = null;
    let startX = 0, startY = 0, panelX = 0, panelY = 0;

    // Reset to the default (bottom-right) position. Shared by double-click
    // (mouse) and long-press (touch).
    const resetPanel = () => {
      panel.style.left = panel.style.top = 'auto';
      panel.style.right = '16px';
      panel.style.bottom = '80px';
      GM_setValue('panel_pos', null);
    };

    handle.addEventListener('pointerdown', e => {
      // Single-pointer drag: ignore a second touch/pen mid-drag and non-left/
      // non-primary pointers, so the start origin can't be clobbered.
      if (dragging || !e.isPrimary || e.button !== 0) return;
      e.preventDefault(); // block text-selection + synthetic mouse events on the handle
      dragging = true;
      activePointerId = e.pointerId;
      startX = e.clientX;
      startY = e.clientY;
      const rect = panel.getBoundingClientRect();
      panelX = rect.left;
      panelY = rect.top;
      // Capture: route every subsequent move/up to the handle even if the cursor
      // passes over the Twitch player iframe (the original bug). Guarded so an
      // exotic UA that throws here doesn't leave us stuck mid-drag.
      try { handle.setPointerCapture(e.pointerId); } catch (_) { /* capture optional */ }
      // Long-press (hold still ~600ms) resets position — touch-friendly
      // counterpart to double-click, which is unreliable on touchscreens.
      pressTimer = setTimeout(() => {
        pressTimer = null;
        dragging = false;
        try { handle.releasePointerCapture(activePointerId); } catch (_) {}
        activePointerId = null;
        resetPanel();
      }, 600);
    });

    handle.addEventListener('pointermove', e => {
      if (!dragging || e.pointerId !== activePointerId) return;
      // Any real movement means this is a drag, not a long-press → cancel reset.
      if (pressTimer && (Math.abs(e.clientX - startX) > 4 || Math.abs(e.clientY - startY) > 4)) {
        clearTimeout(pressTimer); pressTimer = null;
      }
      const c = clamp(panelX + (e.clientX - startX), panelY + (e.clientY - startY));
      panel.style.left = c.left + 'px';
      panel.style.top  = c.top  + 'px';
      panel.style.right  = 'auto';
      panel.style.bottom = 'auto';
    });

    const endDrag = e => {
      // Only the active pointer ends the drag; a stray pointer's up/cancel is ignored.
      if (!dragging || (e && e.pointerId !== activePointerId)) return;
      if (pressTimer) { clearTimeout(pressTimer); pressTimer = null; } // quick tap ≠ reset
      dragging = false;
      try { handle.releasePointerCapture(activePointerId); } catch (_) {}
      activePointerId = null;
      GM_setValue('panel_pos', { left: panel.style.left, top: panel.style.top });
    };
    handle.addEventListener('pointerup', endDrag);
    handle.addEventListener('pointercancel', endDrag);
    // Authoritative cleanup: if capture is lost any other way (element hidden,
    // device removed, browser policy), clear the flag so the drag can't stick.
    handle.addEventListener('lostpointercapture', endDrag);

    // Double-click the header to reset (mouse escape hatch; long-press for touch).
    handle.addEventListener('dblclick', resetPanel);

    // Re-clamp on viewport changes (window resize, theater-mode toggle) so a
    // saved position can't strand the panel — and its drag handle — off-screen.
    window.addEventListener('resize', () => {
      if (!panel.style.left || panel.style.left === 'auto') return; // still default-anchored
      const c = clamp(parseInt(panel.style.left, 10) || 0, parseInt(panel.style.top, 10) || MIN_TOP);
      panel.style.left = c.left + 'px';
      panel.style.top  = c.top  + 'px';
    });
  })();

  // ── Save config ───────────────────────────────────────────────────────────
  document.getElementById('wos-save-cfg').addEventListener('click', () => {
    ollamaBase  = document.getElementById('wos-ollama-base').value.trim().replace(/\/$/, '');
    visionModel = document.getElementById('wos-vision-model').value.trim();
    const newDictUrl = document.getElementById('wos-dict-url').value.trim();
    const dictUrlChanged = newDictUrl && newDictUrl !== dictUrl;
    if (newDictUrl) dictUrl = newDictUrl; // don't let a cleared field blank the URL
    useClaude   = document.getElementById('wos-use-claude').checked;
    GM_setValue('ollama_base',        ollamaBase);
    GM_setValue('vision_model',       visionModel);
    GM_setValue('dict_url',           dictUrl);
    GM_setValue('use_claude_vision',  useClaude);
    // A new dict URL must invalidate the cache, otherwise ensureDict() keeps
    // serving the old cached wordlist (cache-first) until a manual 🔁 Dict.
    if (dictUrlChanged) {
      dictGen++; // supersede any in-flight fetch of the previous URL
      dictSet = dictByKey = freqRank = null;
      dictLoading = null;
      GM_setValue(DICT_CACHE_KEY, '');
      setDictStatus();
      ensureDict().then(setDictStatus);
    }
    const s = document.getElementById('wos-cfg-status');
    s.textContent = '✓ Saved';
    setTimeout(() => { s.textContent = ''; }, 2000);
  });

  // ── Dict UI status + refresh ──────────────────────────────────────────────
  function setDictStatus() {
    const el = document.getElementById('wos-dict-status');
    if (!el) return;
    if (dictByKey) {
      el.textContent = `📚 Dict: ${dictSet.size.toLocaleString()} words`;
      el.style.color = '#4ade80';
    } else if (dictLoading) {
      el.textContent = '⏳ Dict loading…';
      el.style.color = '#facc15';
    } else {
      el.textContent = '⚠ Dict not loaded — click 🔁 Dict';
      el.style.color = '#f87171';
    }
  }

  // Refresh: await any in-flight load before clearing state to avoid a race
  // where the old fetch resolves and overwrites a fresh index.
  document.getElementById('wos-refresh-dict').addEventListener('click', async () => {
    if (dictLoading) { try { await dictLoading; } catch (_) { /* ignore */ } }
    dictSet = dictByKey = freqRank = null;
    dictLoading = null;
    GM_setValue(DICT_CACHE_KEY, ''); // fetchDict will overwrite
    setDictStatus();
    try {
      await fetchDict(dictUrl);
    } catch (e) {
      console.error('[WoS] Dict refresh failed', e);
    }
    setDictStatus();
  });

  // Load dictionary from a user-picked local file. Bypasses network entirely —
  // useful when raw.githubusercontent.com is blocked or any fetch path silently
  // fails. Cached into GM storage on success so next reload reuses it.
  document.getElementById('wos-dict-file').addEventListener('change', e => {
    const f = e.target.files && e.target.files[0];
    if (!f) return;
    const setStat = (msg, color) => {
      const el = document.getElementById('wos-dict-status');
      if (el) { el.textContent = msg; el.style.color = color; }
    };
    setStat(`⏳ Reading ${f.name} (${(f.size / 1024 / 1024).toFixed(2)} MB)…`, '#facc15');
    const reader = new FileReader();
    reader.onload = ev => {
      try {
        const text = ev.target.result;
        dictGen++; // supersede any in-flight network fetch (fetchDict checks this)
        buildDictIndex(text);
        GM_setValue(DICT_CACHE_KEY, text);
        setDictStatus();
        console.log('[WoS] Dict loaded from file', f.name);
      } catch (err) {
        console.error('[WoS] Dict file parse failed', err);
        setStat('❌ Parse failed: ' + err.message.slice(0, 40), '#f87171');
      }
    };
    reader.onerror = () => setStat('❌ File read failed', '#f87171');
    reader.readAsText(f);
  });

  // Kick off lazy dict + grade-list loads on script start (non-blocking).
  ensureDict().then(setDictStatus);
  setDictStatus();
  ensureGradeList().then(updateGradeStatus);
  updateGradeStatus();

  // ── Claude vision via claude-relay (subscription CLI, $0 marginal) ────────
  // POSTs the base64 frame to /scan-image; the relay spawns `claude -p` with
  // the image and parses Claude's JSON response. ~15-35s/scan but dramatically
  // more accurate than local VLMs on stylised game-tile fonts.
  function claudeScan(imageBase64) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'POST',
        url: 'http://localhost:8760/scan-image',
        headers: { 'Content-Type': 'application/json' },
        data: JSON.stringify({ image_base64: imageBase64 }),
        timeout: 90000,
        onload: r => {
          if (r.status < 200 || r.status >= 300) {
            return reject(new Error(`scan-image HTTP ${r.status}: ${r.responseText.slice(0, 200)}`));
          }
          try {
            const data = JSON.parse(r.responseText);
            if (!data.letters) return reject(new Error('no letters in response'));
            resolve(data);
          } catch (e) {
            reject(new Error('scan-image returned non-JSON: ' + r.responseText.slice(0, 200)));
          }
        },
        onerror: () => reject(new Error('scan-image request failed (claude-relay down?)')),
        ontimeout: () => reject(new Error('scan-image timed out after 90s')),
      });
    });
  }

  // ── Ollama API helper ─────────────────────────────────────────────────────
  // Uses GM_xmlhttpRequest to bypass twitch.tv CSP + CORS.
  // Uses Ollama's native /api/chat multimodal format (images as sibling array,
  // not OpenAI-style content-parts — that format is silently dropped here).
  function ollamaChat(model, userText, imageBase64 = null) {
    const message = imageBase64
      ? { role: 'user', content: userText, images: [imageBase64] }
      : { role: 'user', content: userText };
    // num_gpu: 999 forces Ollama to put all layers on GPU. Otherwise it
    // auto-decides offload at load time and can leave a chunk on CPU even
    // when VRAM is available, tanking inference to 60+ s for a single scan.
    const body = { model, stream: false, messages: [message], options: { num_gpu: 999 } };

    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'POST',
        url: `${ollamaBase}/api/chat`,
        headers: { 'Content-Type': 'application/json' },
        data: JSON.stringify(body),
        timeout: 120000,
        onload: r => {
          if (r.status < 200 || r.status >= 300) {
            return reject(new Error(`Ollama ${r.status}: ${r.responseText.slice(0, 200)}`));
          }
          try {
            const data = JSON.parse(r.responseText);
            resolve(data.message?.content || '');
          } catch (e) {
            reject(new Error('Ollama returned non-JSON: ' + r.responseText.slice(0, 200)));
          }
        },
        onerror: () => reject(new Error('Ollama request failed (server down or @connect missing)')),
        ontimeout: () => reject(new Error('Ollama request timed out')),
      });
    });
  }

  // ── Capture screen frame via getDisplayMedia ──────────────────────────────
  // Twitch's <video> element has hardware-decoded pixels that come back blank
  // when drawn to a canvas (browser security on protected streams). The only
  // reliable cross-browser way to get rendered Twitch pixels is to ask the
  // user for screen-share permission via getDisplayMedia. First scan prompts
  // them to pick a window/screen; subsequent scans reuse the stream silently.
  //
  // Downsample to 800px wide — vision models tokenise into patches and a full
  // screen capture would blow through context length and tank inference.
  const SCAN_MAX_WIDTH = 800;
  let screenStream = null;
  let screenVideo  = null;

  async function ensureScreenStream() {
    if (screenStream && screenStream.active && screenVideo && screenVideo.videoWidth > 0) {
      return true;
    }
    try {
      // Release any stale stream before requesting a new one so we don't leak
      // capture tracks (and the browser's "sharing" indicator) on re-share.
      screenStream?.getTracks().forEach(t => t.stop());
      screenStream = await navigator.mediaDevices.getDisplayMedia({
        video: { displaySurface: 'window' },
        audio: false,
      });
      // If the user clicks Chrome's "Stop sharing" banner, reset state so the
      // next scan re-prompts.
      screenStream.getVideoTracks()[0].onended = () => {
        screenStream = null;
        screenVideo  = null;
        setStatus('🎬 Screen share stopped — click 🔍 to re-share', '#facc15');
      };
      screenVideo = document.createElement('video');
      screenVideo.srcObject  = screenStream;
      screenVideo.muted      = true;
      screenVideo.playsInline = true;
      await screenVideo.play();
      // Wait for the first frame; videoWidth is 0 until then.
      for (let i = 0; i < 30 && screenVideo.videoWidth === 0; i++) {
        await new Promise(r => setTimeout(r, 50));
      }
      if (screenVideo.videoWidth === 0) return false;
      // Settle delay: Chrome's screen-share dialog and "tab is sharing"
      // banner can still be visible/animating for ~500ms after the stream
      // becomes ready. Without this wait, the first captured frame contains
      // the share UI overlay instead of the actual stream content.
      await new Promise(r => setTimeout(r, 800));
      return true;
    } catch (e) {
      console.error('[WoS] getDisplayMedia failed:', e);
      screenStream = null;
      screenVideo  = null;
      return false;
    }
  }

  async function captureFrame() {
    const ok = await ensureScreenStream();
    if (!ok) return null;
    const srcW = screenVideo.videoWidth;
    const srcH = screenVideo.videoHeight;
    const scale = Math.min(1, SCAN_MAX_WIDTH / srcW);
    const c = document.createElement('canvas');
    c.width  = Math.round(srcW * scale);
    c.height = Math.round(srcH * scale);
    c.getContext('2d').drawImage(screenVideo, 0, 0, c.width, c.height);
    return c.toDataURL('image/jpeg', 0.85).split(',')[1];
  }

  // ── Render letter chips (clickable to toggle fake) ────────────────────────
  function renderLetters() {
    const wrap = document.getElementById('wos-letters-wrap');
    if (!detectedLetters.length) {
      wrap.innerHTML = '<span class="chip-hint">No scan yet</span>';
      document.getElementById('wos-fake-list').textContent = '';
      return;
    }

    wrap.innerHTML = detectedLetters.map((l, i) => {
      const isFake = fakeLetters.includes(l + ':' + i); // index keys allow duplicate letters
      return `<span class="lchip${isFake ? ' fake' : ''}" data-idx="${i}" title="Click letter to toggle fake. Click ✕ to remove.">
        ${l}<span class="badge" data-remove="${i}" title="Remove this letter">✕</span>
      </span>`;
    }).join('');

    wrap.querySelectorAll('.lchip').forEach(chip => {
      chip.addEventListener('click', e => {
        // Click on the ✕ badge → remove this letter (and any fake marker on it),
        // then re-key remaining fake indices to account for the shift.
        if (e.target.classList.contains('badge')) {
          const idx = parseInt(e.target.dataset.remove, 10);
          detectedLetters.splice(idx, 1);
          fakeLetters = fakeLetters
            .filter(k => parseInt(k.split(':')[1], 10) !== idx)
            .map(k => {
              const [letter, iStr] = k.split(':');
              const i = parseInt(iStr, 10);
              return i > idx ? `${letter}:${i - 1}` : k;
            });
          renderLetters();
          updateFakeList();
          if (detectedLetters.length === 0) {
            document.getElementById('wos-btn-genwords').disabled = true;
          }
          return;
        }
        // Click on the chip body → toggle fake state.
        const idx = parseInt(chip.dataset.idx, 10);
        const key = detectedLetters[idx] + ':' + idx;
        if (fakeLetters.includes(key)) {
          fakeLetters = fakeLetters.filter(k => k !== key);
        } else {
          fakeLetters.push(key);
        }
        renderLetters();
        updateFakeList();
      });
    });

    updateFakeList();
  }

  function updateFakeList() {
    const el = document.getElementById('wos-fake-list');
    if (!fakeLetters.length) {
      el.textContent = 'No fake letters marked';
      el.style.color = '#6d28d9';
    } else {
      const names = fakeLetters.map(k => k.split(':')[0]);
      el.textContent = `Fake: ${names.join(', ')} — Real: ${getRealLetters().join(' ')}`;
      el.style.color = '#f87171';
    }
  }

  function getRealLetters() {
    const fakeIndices = new Set(fakeLetters.map(k => parseInt(k.split(':')[1])));
    return detectedLetters.filter((_, i) => !fakeIndices.has(i));
  }

  // ── Scan ──────────────────────────────────────────────────────────────────
  document.getElementById('wos-btn-scan').addEventListener('click', async () => {
    if (scanning) return; // re-entry guard: overlapping scans race on shared state
    scanning = true;
    const scanBtn = document.getElementById('wos-btn-scan');
    const scanBtnLabel = scanBtn.textContent;
    scanBtn.disabled = true;
    scanBtn.textContent = '📸 Scanning…'; // 15–35s with Claude vision — show it's working
    try {
    setStatus('📸 Capturing screen…', '#06b6d4');
    const frame = await captureFrame();
    if (!frame) { setStatus('❌ Screen capture denied or no source picked', '#f87171'); return; }

    setStatus('📸 Scanning with ' + (useClaude ? 'Claude vision (slow)' : visionModel) + '…', '#06b6d4');
    fakeLetters = [];

    // IMPORTANT: do not put concrete letter values in this prompt. Small
    // vision models often echo example values verbatim when the image is
    // hard to read — that's how every scan was returning identical wrong
    // letters regardless of what's actually on screen.
    const prompt = `Look at this screenshot of the Words on Stream game. Find the row of large letter tiles (each tile is a single capital letter with a small number underneath showing point value).

Reply with ONLY this JSON structure, no preamble, no markdown fences, no example values from this prompt — fill in what you actually see:

{"letters":[<one uppercase single-letter string per tile, in left-to-right order>],"fake_letters":[<subset of "letters" identified as fake, where fake tiles typically have higher point values or look visually distinct from the others>],"found_words":[<words already locked in on the scoreboard, if any>]}`;

    try {
      // Two-path scan: Claude CLI (via claude-relay) or local Ollama.
      let info;
      if (useClaude) {
        info = await claudeScan(frame);
        panel._lastRawResponse = JSON.stringify(info, null, 2);
      } else {
        const raw = await ollamaChat(visionModel, prompt, frame);
        panel._lastRawResponse = raw;
        info = extractJSON(raw);
      }
      panel._lastFrame = frame;

      // Validate untrusted LLM output to single A–Z chars before it reaches the
      // innerHTML chip renderer or the solver. Multi-char entries ("CAT") split
      // into letters; injection payloads collapse to nothing.
      detectedLetters = cleanLetters(info.letters);

      // Intentionally NOT auto-marking fakes from the LLM — vision models are
      // unreliable at distinguishing fake tiles, and false positives drop real
      // letters from the word generator. User clicks chips to mark fakes.
      fakeLetters = [];

      renderLetters();
      // Store found words (board-locked) so setWordList can grey them out.
      panel._foundWords = (Array.isArray(info.found_words) ? info.found_words : [])
        .map(cleanWord).filter(w => w.length >= 3);

      if (detectedLetters.length) {
        setStatus('✅ Scanned! Adjust fakes then ⚡ Gen Words', '#4ade80');
        document.getElementById('wos-btn-genwords').disabled = false;
      } else {
        setStatus('⚠ No letters detected — rescan or add them manually', '#facc15');
        document.getElementById('wos-btn-genwords').disabled = true;
      }

    } catch (e) {
      setStatus('❌ Scan error: ' + e.message.slice(0, 45), '#f87171');
      console.error('[WoS scan]', e);
    }
    } finally {
      scanning = false;
      scanBtn.disabled = false;
      scanBtn.textContent = scanBtnLabel; // restore on success, error, or early return
    }
  });

  // ── Generate words ────────────────────────────────────────────────────────
  // Deterministic anagram solver against the local wordlist. No LLM in this
  // path — every generated word is guaranteed dict-valid by construction.
  // If the dict isn't loaded, we abort with a clear error and prompt to Refresh.
  document.getElementById('wos-btn-genwords').addEventListener('click', async () => {
    const real = getRealLetters();
    if (!real.length) { setStatus('⚠ No real letters!', '#facc15'); return; }

    setStatus('⏳ Loading dict…', '#a78bfa');
    const dictReady = await ensureDict();
    setDictStatus();

    if (!dictReady) {
      setStatus('❌ Dict unavailable — check URL + click 🔁 Dict', '#f87171');
      return;
    }

    // Don't pre-filter; setWordList handles min-length + marks chat-found
    // words as sent (grey) without removing them. This shows the full anagram
    // surface so the user can see all options.
    const words = findAnagrams(real);
    setWordList(words);
    setStatus(`✅ ${wordList.length} dict words — click to send`, '#4ade80');
  });

  // ── JSON extractor (handles LLM slop around JSON) ─────────────────────────
  // Multi-strategy: tries every balanced {...} candidate with trailing-comma
  // fix as backup; if all parse attempts fail, falls back to regex-extracting
  // the three arrays the scan path actually cares about. Tolerant of
  // preamble/commentary text that smaller models often add around their JSON.
  function extractJSON(text) {
    const cleaned = text.replace(/```json|```/g, '').trim();

    // Strategy 1: walk every {...} block, try strict parse then comma-fixed.
    for (let start = 0; start < cleaned.length; start++) {
      if (cleaned[start] !== '{') continue;
      let depth = 0;
      for (let i = start; i < cleaned.length; i++) {
        if (cleaned[i] === '{') depth++;
        else if (cleaned[i] === '}') {
          depth--;
          if (depth === 0) {
            const candidate = cleaned.slice(start, i + 1);
            // Only accept a block that actually carries a letters array — a bare
            // {} or a reasoning-note object in the preamble would otherwise parse
            // first and silently yield an empty scan.
            try { const o = JSON.parse(candidate); if (Array.isArray(o.letters)) return o; } catch (_) {}
            // Try fixing common LLM JSON sins: trailing commas before } or ].
            try { const o = JSON.parse(candidate.replace(/,(\s*[}\]])/g, '$1')); if (Array.isArray(o.letters)) return o; } catch (_) {}
            break; // skip past this {...} block, try next
          }
        }
      }
    }

    // Strategy 2: regex extract just the arrays our scan path needs.
    const extractArr = key => {
      const m = cleaned.match(new RegExp(`"${key}"\\s*:\\s*\\[([^\\]]*)\\]`, 'i'));
      if (!m) return [];
      return [...m[1].matchAll(/"([A-Za-z]+)"/g)].map(x => x[1]);
    };
    const arrays = {
      letters:      extractArr('letters'),
      fake_letters: extractArr('fake_letters'),
      found_words:  extractArr('found_words'),
    };
    if (arrays.letters.length > 0) return arrays;

    console.warn('[WoS] extractJSON: no parseable JSON in:', text);
    throw new Error('LLM returned no parseable JSON (see console)');
  }

  // ── Dictionary: anagram solver ────────────────────────────────────────────
  // Wordlist (ENABLE1 default) fetched once via GM_xmlhttpRequest, cached in
  // GM storage under a versioned key (DICT_CACHE_KEY, hoisted to top of IIFE).
  // Two structures share one indexing pass:
  //   - dictSet: O(1) word validation (Set.has)
  //   - dictByKey: Map<sortedLetters, word[]> for anagram lookup
  // Sub-multiset checks run directly on the sorted-letter keys via 2-pointer
  // walk — no Uint8Array sidecar needed.

  function sortedKey(s) {
    return s.split('').sort().join('');
  }

  // True if every char in `a` appears in `b` at least as many times.
  // Both inputs must be sorted strings (uppercase A–Z).
  function isSubKey(a, b) {
    let i = 0, j = 0;
    while (i < a.length && j < b.length) {
      if (a[i] === b[j])      { i++; j++; }
      else if (a[i] > b[j])   {      j++; }
      else                    return false;
    }
    return i === a.length;
  }

  // Accepts both plain wordlists ("word\n") and Norvig-style frequency lists
  // ("word\tcount\n", sorted by descending frequency). For Norvig format,
  // file-order rank becomes the frequency signal used to sort suggestions.
  function buildDictIndex(text) {
    const t0 = Date.now();
    dictSet = new Set();
    dictByKey = new Map();
    freqRank = new Map();
    let rank = 0;
    for (const raw of text.split('\n')) {
      const tab = raw.indexOf('\t');
      const w = (tab >= 0 ? raw.slice(0, tab) : raw).trim().toUpperCase();
      if (w.length < 3 || !/^[A-Z]+$/.test(w) || dictSet.has(w)) continue;
      dictSet.add(w);
      freqRank.set(w, rank++);
      const k = sortedKey(w);
      const bucket = dictByKey.get(k);
      if (bucket) bucket.push(w); else dictByKey.set(k, [w]);
    }
    console.log(`[WoS] Dict indexed: ${dictSet.size} words, ${dictByKey.size} keys, ${Date.now() - t0}ms`);
    return dictSet.size;
  }

  function fetchDict(url) {
    const myGen = ++dictGen; // claim this load; a newer load bumps dictGen past it
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET',
        url,
        timeout: 60000,
        onload: r => {
          if (r.status < 200 || r.status >= 300) return reject(new Error(`Dict HTTP ${r.status}`));
          // A file-pick or refresh that landed while this fetch was in flight
          // already built a fresher index — don't clobber it.
          if (myGen !== dictGen) return resolve(dictSet ? dictSet.size : 0);
          try {
            GM_setValue(DICT_CACHE_KEY, r.responseText);
            resolve(buildDictIndex(r.responseText));
          } catch (e) { reject(e); }
        },
        onerror: () => reject(new Error('Dict fetch failed (network)')),
        ontimeout: () => reject(new Error('Dict fetch timeout')),
      });
    });
  }

  // Lazy loader: build index from cache on first call, fetch if cache empty.
  // dictLoading is hoisted to the top of the IIFE (see comment up there).
  function ensureDict() {
    if (dictByKey) return Promise.resolve(true);
    if (dictLoading) return dictLoading;
    dictLoading = (async () => {
      try {
        const cached = GM_getValue(DICT_CACHE_KEY, null);
        if (cached) {
          buildDictIndex(cached);
          return true;
        }
        await fetchDict(dictUrl);
        return true;
      } catch (e) {
        // A corrupt cache used to throw OUTSIDE the try, leaving dictLoading as a
        // permanently-rejected promise that bricked every later ensureDict call.
        // Clear the bad cache and null dictLoading so the next call refetches.
        console.warn('[WoS] Dict unavailable:', e.message);
        GM_setValue(DICT_CACHE_KEY, '');
        dictLoading = null; // allow retry
        return false;
      }
    })();
    return dictLoading;
  }

  // ── Grade-level data (AoA-derived) ────────────────────────────────────────
  // Parses a `WORD\tgrade` TSV into gradeMap. Mirrors the dict loader: GM-cached,
  // generation-guarded so an in-flight fetch can't clobber a fresher load.
  function buildGradeIndex(text) {
    const m = new Map();
    for (const raw of text.split('\n')) {
      const tab = raw.indexOf('\t');
      if (tab < 0) continue;
      const w = raw.slice(0, tab).trim().toUpperCase();
      const g = parseInt(raw.slice(tab + 1), 10);
      if (w && /^[A-Z]+$/.test(w) && g >= 0 && g <= 12) m.set(w, g);
    }
    gradeMap = m;
    console.log(`[WoS] Grades indexed: ${m.size} words`);
    return m.size;
  }

  function fetchGradeList(url) {
    const myGen = ++gradeGen;
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET', url, timeout: 60000,
        onload: r => {
          if (r.status < 200 || r.status >= 300) return reject(new Error(`Grades HTTP ${r.status}`));
          if (myGen !== gradeGen) return resolve(gradeMap ? gradeMap.size : 0);
          try { GM_setValue(GRADE_CACHE_KEY, r.responseText); resolve(buildGradeIndex(r.responseText)); }
          catch (e) { reject(e); }
        },
        onerror: () => reject(new Error('Grades fetch failed (network)')),
        ontimeout: () => reject(new Error('Grades fetch timeout')),
      });
    });
  }

  // Lazy loader; never throws to callers — grade filtering degrades to the
  // frequency proxy if this fails.
  function ensureGradeList() {
    if (gradeMap) return Promise.resolve(true);
    if (gradeLoading) return gradeLoading;
    gradeLoading = (async () => {
      try {
        const cached = GM_getValue(GRADE_CACHE_KEY, null);
        if (cached) {
          buildGradeIndex(cached);
          if (gradeMap.size >= 1000) return true;
          // Truncated/corrupt cache (the real list has ~31k) — drop and refetch.
          gradeMap = null;
          GM_setValue(GRADE_CACHE_KEY, '');
        }
        await fetchGradeList(gradeUrl);
        return true;
      } catch (e) {
        console.warn('[WoS] Grade list unavailable (using frequency proxy):', e.message);
        GM_setValue(GRADE_CACHE_KEY, '');
        gradeLoading = null;
        return false;
      }
    })();
    return gradeLoading;
  }

  // Approximate grade for words NOT in the AoA dataset, from their frequency rank
  // in the loaded dict (more common ⇒ lower grade). Coarse but monotonic.
  function gradeFromFreq(rank) {
    if (rank == null || !isFinite(rank)) return 12;
    if (rank < 1000)  return 2;
    if (rank < 3000)  return 4;
    if (rank < 8000)  return 6;
    if (rank < 20000) return 8;
    if (rank < 60000) return 10;
    return 12;
  }

  // A word's effective grade: real AoA grade if known, else frequency-derived.
  function effectiveGrade(word) {
    const g = gradeMap && gradeMap.get(word);
    return g != null ? g : gradeFromFreq(freqRank ? freqRank.get(word) : null);
  }

  function updateGradeStatus() {
    const el = document.getElementById('wos-grade-status');
    if (!el) return;
    const loaded = gradeMap && gradeMap.size > 0;
    el.textContent = loaded ? `${gradeMap.size.toLocaleString()}w` : 'freq';
    el.style.color = loaded ? '#a78bfa' : '#facc15'; // yellow flags the fallback
    el.title = loaded
      ? `${gradeMap.size.toLocaleString()} graded words loaded`
      : 'grade list not loaded — using a frequency estimate';
  }

  // All dict words whose sorted-letter key is a sub-multiset of `letters`.
  // Returns [] (never null) when dict is unloaded so callers can chain freely.
  // Sort priority: lower freq-rank (more common) first, then length desc,
  // then alphabetical. With a Norvig-style frequency list as the dict, this
  // surfaces game-likely words at the top; with a plain wordlist, freqRank
  // tracks file-order which falls through to the length/alpha tiebreakers.
  function findAnagrams(letters) {
    if (!dictByKey) return [];
    const availKey = sortedKey(letters.join(''));
    const found = [];
    for (const [k, bucket] of dictByKey) {
      if (k.length > availKey.length) continue;
      if (isSubKey(k, availKey)) for (const w of bucket) found.push(w);
    }
    found.sort((a, b) => {
      const ra = freqRank?.get(a) ?? Infinity;
      const rb = freqRank?.get(b) ?? Infinity;
      if (ra !== rb) return ra - rb;
      return b.length - a.length || a.localeCompare(b);
    });
    return found;
  }

  // wos.gg solver: each tile commits to ONE letter for the round. Enumerate
  // all 2^n letter-choice combinations (n ≤ 8 → ≤256 combos) and pick the one
  // whose achievable words sum to the highest length-squared score. Length²
  // is a superlinear proxy for game scoring — one 7-letter bingo (49) beats
  // five 3-letter words (45). Refine with real WoS point values once we have
  // round telemetry.
  //
  // Performance: the naive "scan whole dict per mask" approach is O(2^n × |dict|)
  // and pegged the main thread on full ENABLE1. Instead, scan the dict ONCE
  // against the union pool (every letter that could appear in any tile choice),
  // then for each mask filter that small pre-cut set. Cuts a round from ~256
  // full dict scans to 1 + 256 small-list passes.
  function bestTileCombination(tiles) {
    if (!dictByKey) return null;
    const n = tiles.length;
    const empty = { letters: [], words: [], score: 0, mask: 0 };

    // Pool multiset: for each letter, max # of tiles that could contribute it.
    const poolMax = Object.create(null);
    for (const tile of tiles) {
      const seenThisTile = new Set();
      for (const cand of tile) {
        if (seenThisTile.has(cand.letter)) continue;
        seenThisTile.add(cand.letter);
        poolMax[cand.letter] = (poolMax[cand.letter] || 0) + 1;
      }
    }
    const poolLetters = [];
    for (const L in poolMax) for (let i = 0; i < poolMax[L]; i++) poolLetters.push(L);

    // Single full-dict scan for the round. Every word playable under any mask
    // is in this set; per-mask work below is just a sub-multiset filter.
    const poolWords = findAnagrams(poolLetters);
    if (!poolWords.length) return empty;
    const poolKeys = poolWords.map(sortedKey);

    let best = empty;
    for (let mask = 0; mask < (1 << n); mask++) {
      const letters = new Array(n);
      for (let i = 0; i < n; i++) letters[i] = tiles[i][(mask >> i) & 1].letter;
      const maskKey = sortedKey(letters.join(''));

      const words = [];
      let score = 0;
      for (let i = 0; i < poolWords.length; i++) {
        if (isSubKey(poolKeys[i], maskKey)) {
          const w = poolWords[i];
          words.push(w);
          score += w.length * w.length;
        }
      }
      if (score > best.score) best = { letters, words, score, mask };
    }
    return best;
  }

  // ── Chat send ─────────────────────────────────────────────────────────────
  function getChatInput() {
    return (
      document.querySelector('[data-a-target="chat-input"]') ||
      document.querySelector('div[contenteditable="true"][data-test-selector="chat-input"]') ||
      document.querySelector('div[contenteditable="true"].chat-input__textarea') ||
      document.querySelector('div[contenteditable="true"][data-slate-editor]') ||
      document.querySelector('div[role="textbox"][contenteditable="true"]')
    );
  }

  // Scrape visible chat for word-like tokens so we don't re-send what's already
  // been guessed (by us or by other players this round).
  function alreadySentWords() {
    const selectors = [
      '[data-a-target="chat-line-message-body"]',
      '[data-a-target="chat-message-text"]',
      '.chat-line__message .text-fragment',
      '.chat-line__message',
    ];
    let nodes = [];
    for (const sel of selectors) {
      nodes = document.querySelectorAll(sel);
      if (nodes.length) break;
    }
    const seen = new Set();
    nodes.forEach(n => {
      const tokens = (n.textContent || '').toUpperCase().match(/[A-Z]{3,}/g);
      if (tokens) tokens.forEach(w => seen.add(w));
    });
    return seen;
  }

  function sendWord(word) {
    const input = getChatInput();
    if (!input) { setStatus('❌ Chat input not found!', '#f87171'); return false; }
    input.focus();

    if (input.tagName === 'TEXTAREA' || input.tagName === 'INPUT') {
      const setter = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value')?.set;
      if (setter) setter.call(input, word);
      input.dispatchEvent(new Event('input',  { bubbles: true }));
      input.dispatchEvent(new Event('change', { bubbles: true }));
    } else {
      // Modern Twitch chat is Slate.js. Setting textContent or using
      // execCommand('insertText') updates the DOM but NOT Slate's controlled
      // state — the send button stays disabled because Slate thinks the editor
      // is empty. Dispatching a synthetic `paste` event with a DataTransfer
      // is the only reliable cross-version Slate input path: Slate has a
      // built-in paste handler that runs through its onChange pipeline.
      const sel = window.getSelection();
      const range = document.createRange();
      range.selectNodeContents(input);
      sel.removeAllRanges();
      sel.addRange(range);
      const dt = new DataTransfer();
      dt.setData('text/plain', word);
      input.dispatchEvent(new ClipboardEvent('paste', {
        clipboardData: dt,
        bubbles: true,
        cancelable: true,
      }));
    }

    setTimeout(() => {
      ['keydown', 'keypress', 'keyup'].forEach(t =>
        input.dispatchEvent(new KeyboardEvent(t, { key: 'Enter', code: 'Enter', keyCode: 13, which: 13, bubbles: true }))
      );
      // Fallback for Twitch builds where synthetic Enter doesn't submit: if our
      // text is still sitting in the editor, click the send button directly.
      const btn = document.querySelector('[data-a-target="chat-send-button"]');
      if (btn && (input.textContent || '').trim()) btn.click();
    }, 150);
    return true;
  }

  // ── Word list (clickable chips → click to send) ──────────────────────────
  // Replaces the old textarea + ▶ Start queue. Each word renders as a chip;
  // a single click types it into Twitch chat AND fires Enter, then marks the
  // chip as sent (faded + strikethrough) so the remaining set is obvious.
  // setWordList(words): a NEW full word set (from Gen Words / Pull / auto-load).
  // Stored UNFILTERED in allWords; applyFilters() derives the visible list. This
  // is what lets a grade change re-widen (raising the grade re-adds words) instead
  // of permanently shrinking the list.
  function setWordList(words, preserveSent = false) {
    // A Send-all run iterates the live wordList; if a NEW source replaces it
    // (Pull, a new auto-loaded round, Gen Words) stop the run so it can't silently
    // continue on a different word set.
    if (sendingAll) stopSendAll('Stopped — word list changed', '#facc15');
    // cleanWord() strips anything but A–Z, so a poisoned wos_round_state word
    // (cross-tab GM write) can't survive into the innerHTML chip renderer.
    allWords = (Array.isArray(words) ? words : []).map(cleanWord);
    applyFilters(preserveSent);
  }

  // applyFilters(): rebuild the visible wordList from the full allWords source
  // using the current min-length + grade selection. Called on every filter change,
  // so the grade is cumulative (≤ selected, includes all lower grades) AND
  // non-destructive — the list updates live and re-widens when you raise the grade.
  function applyFilters(preserveSent = false) {
    const minLen = Math.max(4, parseInt(document.getElementById('wos-min-len').value, 10) || 4);
    // Pre-mark words already visible in Twitch chat (or locked on the board) as
    // "sent" (grey). preserveSent keeps manual click state across a filter rebuild.
    const skip = new Set([...alreadySentWords(), ...(panel._foundWords || [])]);
    const priorSent = preserveSent
      ? new Set(wordList.filter(e => e.sent).map(e => e.word))
      : null;
    wordList = allWords
      .filter(w => w.length >= minLen)
      // Grade filter: keep words at or below the selected grade (cumulative).
      // effectiveGrade() uses real AoA data, else a frequency-derived grade.
      .filter(w => gradeLevel === 'all' || effectiveGrade(w) <= gradeLevel)
      .map(w => ({ word: w, sent: skip.has(w) || (priorSent ? priorSent.has(w) : false) }));
    renderWordList();
  }

  function renderWordList() {
    const container = document.getElementById('wos-words-list');
    if (!container) return;
    // Update the section-title count. Format: "(X)" if all unsent, or
    // "(X / Y)" where X = remaining, Y = total, after the first send.
    const countEl = document.getElementById('wos-words-count');
    if (countEl) {
      const total = wordList.length;
      const remaining = remainingCount();
      countEl.textContent = remaining === total ? `(${total})` : `(${remaining} / ${total})`;
    }
    if (!wordList.length) {
      container.innerHTML = '<span style="font-size:.65rem;color:#6d28d9;letter-spacing:1px;align-self:center;padding:8px;">No words yet — scan or pull</span>';
      return;
    }
    // Group chips under grade headings (K, 1 … 12), ascending — common/easy words
    // on top, rarer high-grade words below. data-i still indexes the live wordList,
    // so the click handler below is unchanged.
    const groups = new Map();
    wordList.forEach((w, i) => {
      const g = effectiveGrade(w.word);
      if (!groups.has(g)) groups.set(g, []);
      groups.get(g).push(i);
    });
    const gradeLabel = g => (g === 0 ? 'K' : String(g));
    container.innerHTML = [...groups.keys()].sort((a, b) => a - b).map(g =>
      `<div class="wos-grade-group"><span class="wos-grade-label">Grade ${gradeLabel(g)}</span>` +
      groups.get(g).map(i =>
        `<span class="wos-word-chip${wordList[i].sent ? ' sent' : ''}" data-i="${i}">${wordList[i].word}</span>`
      ).join('') +
      `</div>`
    ).join('');
    container.querySelectorAll('.wos-word-chip').forEach(chip => {
      chip.addEventListener('click', () => {
        const i = parseInt(chip.dataset.i, 10);
        const entry = wordList[i];
        if (!entry || entry.sent) return;
        if (!getChatInput()) { setStatus('❌ Open Twitch chat!', '#f87171'); return; }
        // Send lowercase — Twitch's WoS round bot is case-insensitive but the
        // chat audience reads lowercase as less spammy / shouty.
        // Only mark sent if the chat input was actually found and populated;
        // sendWord returns false when the editor is missing.
        if (!sendWord(entry.word.toLowerCase())) return;
        entry.sent = true;
        renderWordList();
        const remaining = remainingCount();
        setStatus(`Sent ${entry.word} · ${remaining} left`, '#4ade80');
      });
    });
  }

  // ── Pull words from wos.gg tab ────────────────────────────────────────────
  document.getElementById('wos-btn-pull').addEventListener('click', () => {
    const state = GM_getValue('wos_round_state', null);
    if (!isValidRoundState(state)) {
      setStatus('⚠ No valid wos.gg data — open the companion tab', '#facc15');
      return;
    }
    const ageMs = Date.now() - state.ts;
    const ageSec = Math.round(ageMs / 1000);
    // NaN-safe: a missing/old ts (older script version) must also be rejected;
    // `ageMs <= STATE_STALE_MS` is false for NaN.
    if (!(ageMs <= STATE_STALE_MS)) {
      setStatus(`⚠ wos.gg data ${isNaN(ageMs) ? 'has no timestamp' : `is ${ageSec}s old`} — rescan there`, '#facc15');
      return;
    }
    if (!state.words.length) {
      setStatus('⚠ wos.gg has no words yet', '#facc15');
      return;
    }
    // setWordList marks chat-already-said words as sent (grey) rather than
    // removing them, so the user sees the full set.
    setWordList(state.words);
    const remaining = remainingCount();
    setStatus(`✅ Pulled ${remaining}/${wordList.length} words (L${state.level}, ${ageSec}s old)`, '#4ade80');
  });

  // ✕ Letters — clears only the scan-letter chips + fake state. Word
  // suggestions stay so you can tweak min-len/grade and re-gen.
  document.getElementById('wos-btn-clear-letters').addEventListener('click', () => {
    detectedLetters = [];
    fakeLetters = [];
    panel._foundWords = [];
    renderLetters();
    document.getElementById('wos-btn-genwords').disabled = true;
    setStatus('Letters cleared', '#a78bfa');
  });

  // ✕ Words — clears only the suggestion chips. Letters stay so you can
  // generate again with different settings.
  document.getElementById('wos-btn-clear').addEventListener('click', () => {
    if (sendingAll) stopSendAll();
    wordList = [];
    renderWordList();
    setStatus('Words cleared', '#a78bfa');
  });

  // ▶ Send all — fire the unsent chips in sequence, spaced ~1.7s to stay under
  // Twitch's chat rate-limit. Click again (⏹ Stop) to halt. Sends only words
  // currently in the list (respects min-len + grade filter) and only unsent ones.
  const sendAllBtn = document.getElementById('wos-btn-sendall');
  const stopSendAll = (msg, color = '#4ade80') => {
    sendingAll = false;
    if (sendAllTimer) { clearTimeout(sendAllTimer); sendAllTimer = null; }
    sendAllBtn.textContent = '▶ Send all';
    sendAllBtn.classList.remove('btn-stop'); sendAllBtn.classList.add('btn-start');
    if (msg) setStatus(msg, color);
  };
  sendAllBtn.addEventListener('click', () => {
    if (sendingAll) { stopSendAll('Stopped'); return; }
    if (!wordList.some(e => !e.sent)) { setStatus('⚠ No unsent words', '#facc15'); return; }
    if (!getChatInput()) { setStatus('❌ Open Twitch chat!', '#f87171'); return; }
    sendingAll = true;
    sendAllBtn.textContent = '⏹ Stop';
    sendAllBtn.classList.remove('btn-start'); sendAllBtn.classList.add('btn-stop');
    setStatus(`Sending… ${remainingCount()} left`, '#4ade80'); // immediate feedback
    const step = () => {
      if (!sendingAll) return;
      const entry = wordList.find(e => !e.sent);
      if (!entry) { stopSendAll('✅ Sent all'); return; }
      if (!getChatInput()) { stopSendAll('❌ Chat input lost', '#f87171'); return; }
      // Schedule the next word ONLY on a successful send — otherwise a failing
      // sendWord would re-arm a 1.7s retry on the same entry forever.
      if (sendWord(entry.word.toLowerCase())) {
        entry.sent = true;
        renderWordList();
        setStatus(`Sending… ${remainingCount()} left`, '#4ade80');
        sendAllTimer = setTimeout(step, 1700);
      } else {
        stopSendAll('❌ Send failed — stopped', '#f87171');
      }
    };
    step();
  });

  // Debug: open the most recent scanned frame in a new tab so you can see
  // exactly what the vision model received.
  document.getElementById('wos-btn-debug-frame').addEventListener('click', () => {
    if (!panel._lastFrame) {
      setStatus('⚠ No scan yet — click 🔍 first', '#facc15');
      return;
    }
    const w = window.open();
    if (!w) { setStatus('⚠ Pop-up blocked', '#facc15'); return; }
    w.document.title = 'WoS · last captured frame';
    w.document.body.style.cssText = 'margin:0;background:#0f0a1e';
    const img = w.document.createElement('img');
    img.src = 'data:image/jpeg;base64,' + panel._lastFrame;
    img.style.cssText = 'max-width:100%;display:block;margin:auto';
    w.document.body.appendChild(img);
  });

  // Debug: dump the raw AI response text into a new tab for inspection.
  document.getElementById('wos-btn-debug-raw').addEventListener('click', () => {
    if (!panel._lastRawResponse) {
      setStatus('⚠ No scan yet — click 🔍 first', '#facc15');
      return;
    }
    const w = window.open();
    if (!w) { setStatus('⚠ Pop-up blocked', '#facc15'); return; }
    w.document.title = 'WoS · last AI output';
    w.document.body.style.cssText = 'margin:0;padding:16px;background:#0f0a1e;color:#e9d5ff;font-family:monospace;white-space:pre-wrap';
    w.document.body.textContent = panel._lastRawResponse;
  });

  // Auto-refresh: when the wos.gg tab writes a new round state, refill the
  // chip list automatically. Cross-tab notification via Tampermonkey's
  // shared-storage listener — no polling, fires within a few ms of the write.
  GM_addValueChangeListener('wos_round_state', (_key, _old, newVal, remote) => {
    if (!remote || !isValidRoundState(newVal)) return;
    if (Date.now() - newVal.ts > STATE_STALE_MS) return; // ignore stale/replayed writes
    // Pass the full list (same as Pull) — setWordList greys chat-seen words
    // rather than dropping them, so the auto path and Pull stay consistent.
    setWordList(newVal.words);
    const remaining = remainingCount();
    setStatus(`🔄 Auto-loaded L${newVal.level} · ${remaining}/${wordList.length} words`, '#4ade80');
  });

  // Initial render so the empty-state message shows up.
  renderWordList();

  // Stop the screen-capture stream when the tab goes away so the capture track
  // (and the browser "sharing" indicator) doesn't leak.
  window.addEventListener('pagehide', () => {
    screenStream?.getTracks().forEach(t => t.stop());
  });

  function setStatus(msg, color = '#a78bfa') {
    const el = document.getElementById('wos-status');
    if (el) { el.textContent = msg; el.style.color = color; }
  }

  // ── wos.gg companion mode ─────────────────────────────────────────────────
  // Reads tiles directly from the DOM (no vision needed), pre-generates words
  // on level change, writes them to GM shared storage so the Twitch tab can
  // pull them via the 📥 button.
  function runWosGgMode() {
    const badge = document.createElement('div');
    badge.id = 'wos-gg-badge';
    badge.style.cssText = 'position:fixed;bottom:16px;right:16px;z-index:99999;'
      + 'background:#0f0a1e;color:#c084fc;border:1px solid #7c3aed;border-radius:8px;'
      + 'padding:8px 12px;font:11px/1.4 "Segoe UI",sans-serif;letter-spacing:1px;'
      + 'box-shadow:0 0 14px rgba(168,85,247,.5);max-width:300px;';
    badge.textContent = 'WOS · waiting for tiles…';
    const mount = () => { if (document.body) document.body.appendChild(badge); else setTimeout(mount, 100); };
    mount();
    const setBadge = (msg, color) => {
      badge.textContent = msg;
      badge.style.color = color || '#c084fc';
    };

    const readHeading = label => {
      const h5 = [...document.querySelectorAll('h5')].find(h => h.textContent.trim() === label);
      return h5?.parentElement?.querySelector('h3')?.textContent?.trim() || null;
    };
    // Strict tile-row match: exactly 2 children (one real, one fake letter).
    // Looser >= 2 silently captured 3+-child rows as malformed data.
    const readTiles = () => [...document.querySelectorAll('ul')]
      .map(ul => [...ul.children])
      .filter(lis => lis.length === 2 && lis.every(li => li.tagName === 'LI' && li.querySelector('span')))
      .map(lis => lis.map(li => ({
        letter: (li.childNodes[0]?.textContent || '').trim().toUpperCase(),
        points: parseInt(li.querySelector('span')?.textContent || '0', 10),
      })))
      .filter(tile => tile.every(c => /^[A-Z]$/.test(c.letter)));

    let lastKey = null;
    let busy = false;
    // Identify a round by its level label AND its tile contents, so a new round
    // that reuses the same "LEVEL n" label (different tiles) still re-solves.
    const roundKey = (level, tiles) =>
      level + '|' + tiles.map(t => t.map(c => c.letter).sort().join('')).join(',');
    async function tick() {
      if (busy) return;
      const level = readHeading('LEVEL');
      if (!level) return;
      const tiles = readTiles();
      if (!tiles.length) return;
      // Guard the 2^n combinator: a real WoS row is ≤9 tiles. More than that
      // means readTiles matched spurious 2-<li> lists elsewhere on the page —
      // solving them would be wrong and could freeze the tab.
      if (tiles.length > 9) {
        setBadge(`WOS · L${level} · ${tiles.length} tile-rows matched (expected ≤9) — skipping`, '#facc15');
        return;
      }
      const key = roundKey(level, tiles);
      if (key === lastKey) return;

      busy = true;
      const goal = readHeading('GOAL');
      setBadge(`WOS · LEVEL ${level} · solving ${tiles.length} tiles…`, '#06b6d4');
      try {
        if (!(await ensureDict())) {
          setBadge(`WOS · L${level} · dict unavailable — open Twitch tab → 🔁 Dict (needs raw.githubusercontent.com)`, '#f87171');
          return; // do NOT commit lastKey — retry on next tick once dict loads
        }
        // The round may have advanced while the dict was loading; re-read and
        // bail if so, rather than publishing stale words for the wrong round.
        if (readHeading('LEVEL') !== level) return;
        const best = bestTileCombination(tiles);
        if (!best || !best.words.length) {
          setBadge(`WOS · L${level} · no playable words for these tiles`, '#facc15');
          lastKey = key; // valid (empty) solve — don't re-solve the same tiles
          return;
        }
        const state = {
          level, goal,
          tilePairs: tiles.map(t => t.map(c => c.letter)),
          letters: best.letters,
          words: best.words,
          ts: Date.now(),
        };
        GM_setValue('wos_round_state', state);
        lastKey = key; // only commit after a successful solve
        setBadge(`WOS · L${level} · ${best.letters.join(' ')} · ${best.words.length} words → Twitch`, '#4ade80');
      } catch (e) {
        setBadge(`WOS · LEVEL ${level} · solve failed: ${e.message.slice(0, 40)} · retrying`, '#f87171');
        console.error('[wos.gg] solve failed', e);
      } finally {
        busy = false;
      }
    }

    const tickId = setInterval(tick, 800);
    window.addEventListener('pagehide', () => clearInterval(tickId));
  }

})();

# wos-data

Data file for the **Words on Stream** auto-guesser userscript (lives in a private
repo; this public repo just hosts the data so the userscript can fetch it via
`raw.githubusercontent.com` unauthenticated).

## `grade-words.tsv`
`WORD<TAB>grade` — 31,067 English words mapped to a US school grade (0 = K … 12).
Derived from the **Kuperman, Stadthagen-Gonzalez & Brysbaert (2012)** age-of-acquisition
norms: `grade = clamp(round(meanAoA − 5), 0, 12)`, filtered to A–Z words ≥3 letters.
The AoA norms are freely available for research; this is a derived lookup table for
personal tooling.

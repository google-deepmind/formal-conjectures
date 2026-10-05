# Benchmark inputs

Lean files are exact historical FC files, retained under the repository's Apache-2.0 license.
The catalog records their commit provenance. `context-R*.txt` files are authored scenarios.

Source snapshots retain the original URL, retrieval date and raw-response hash. HTML snapshots
were reduced to the statement and directly relevant remarks, with markup converted to text.
They are on-demand evaluation inputs, not independently verified answer keys.

- Erdős snapshots come from the named problem pages at [erdosproblems.com](https://www.erdosproblems.com/).
- OEIS snapshots retain the entry authors and the [OEIS End-User License Agreement](https://oeis.org/LICENSE) notice.
- The Jacobson, irrationality, Ramsey and Legendre snapshots are excerpts by Wikipedia contributors,
  adapted to plain text under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
  Each excerpt links its original article, where its authors and edit history are available.

All candidate and source bytes used by the runner have SHA-256 entries in `benchmark.json`.

# Subsets

This directory contains curated, fixed-size subsets of problems from the
repository, intended for use as benchmark evaluation sets.

Each file defines a list of 100 problem names drawn from the repository:

-   **FC100OpenSet1** — 100 randomly sampled open research problems.
-   **FC100SolvedSet1** — 100 randomly sampled problems across the research
    solved, textbook, API, and test categories.

The lists reference problems by `Name` (via the `decl_name%` elaborator) and
include a compile-time check verifying the expected category counts.

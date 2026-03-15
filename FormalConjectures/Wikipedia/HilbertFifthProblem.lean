/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.HilbertProblems.«5»

/-!
# Hilbert's Fifth Problem

The actual formalization is in `FormalConjectures.HilbertProblems.«5»`.

Hilbert's fifth problem asks whether every locally Euclidean topological group admits a Lie group
structure. This was resolved affirmatively by Gleason, Montgomery, and Zippin in 1952.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%27s_fifth_problem)
- [Gleason 1952](https://doi.org/10.2307/1969548)
- [Montgomery–Zippin 1952](https://doi.org/10.2307/1969549)
- [Tao's blog](https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/)
-/

namespace HilbertFifthProblem

@[category research solved, AMS 22 57]
theorem hilbert_fifth_problem : type_of% @HilbertSmith.hilbert_fifth_problem := by
  sorry

end HilbertFifthProblem

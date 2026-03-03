/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 196

*Reference:* [erdosproblems.com/196](https://www.erdosproblems.com/196)
-/
namespace Erdos196

/-- Must every permutation of $\mathbb{N}$, contain a monotone 4-term arithmetic progression?-/
@[category research open, AMS 5 11]
theorem erdos_196 : answer(sorry) ↔ ∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4 := by
  sorry

/--
Davis, Entringer, Graham, and Simmons (1977) proved that every permutation of $\mathbb{N}$
contains a monotone 3-term arithmetic progression, establishing the $k=3$ case; the
problem of whether $k=4$ holds for all permutations remains open.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/196", AMS 5 11]
theorem erdos_196.variants.monotone_3ap :
    ∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 3 := by
  sorry

end Erdos196

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 19

*References:*
- [erdosproblems.com/19](https://www.erdosproblems.com/19)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25–42.
-/

@[expose] public section

namespace Erdos19

open SimpleGraph

/--
If $G$ is an edge-disjoint union of $n$ copies of $K_n$ then is $\chi(G)=n$?
-/
@[category research open, AMS 5]
theorem erdos_19 : answer(sorry) ↔
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), C.graph.chromaticNumber = n := by
  sorry

/-- The conjecture holds for $n \le 3$. -/
@[category textbook, AMS 5]
theorem erdos_19.variants.le_three {V : Type*} {n : ℕ} (C : EFLConfig V n)
    (hn : n ≤ 3) : C.graph.chromaticNumber = n :=
  C.chromaticNumber_eq_of_le_three hn

end Erdos19

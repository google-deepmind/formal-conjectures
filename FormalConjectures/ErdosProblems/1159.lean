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

import FormalConjecturesUtil

/-!
# Erdős Problem 1159

*Reference:* [erdosproblems.com/1159](https://www.erdosproblems.com/1159)
-/

open Configuration

namespace Erdos1159

/--
Determine whether there exists a constant $C>1$ such that the following holds.

Let $P$ be a finite [projective plane](https://en.wikipedia.org/wiki/Projective_plane). Must there exist a set of points $S$ such that $1\leq \lvert S\cap \ell\rvert \leq C$ for all lines $\ell$?
-/
@[category research open, AMS 5 51]
theorem erdos_1159 :
    (∃ C : ℕ, 1 < C ∧
      ∀ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
        ∀ _ : ProjectivePlane P L, ∃ S : Set P, ∀ l : L,
          1 ≤ (S ∩ {p : P | p ∈ l}).ncard ∧ (S ∩ {p : P | p ∈ l}).ncard ≤ C) ↔
      answer(sorry) := by
  sorry

end Erdos1159

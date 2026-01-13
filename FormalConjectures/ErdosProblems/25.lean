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
# Erdős Problem 25

*Reference:* [erdosproblems.com/25](https://www.erdosproblems.com/25)
-/

open Filter Finset Real Nat Set
open scoped Topology
open Classical

namespace Erdos25

/--
Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class
$a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either $n < n_i$ or
$n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?
-/
@[category research open, AMS 11]
theorem erdos_25 : answer(sorry) ↔
    ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
      ∃ d, Set.HasLogDensity
        { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) } d := by
  sorry

end Erdos25

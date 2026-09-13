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
# Erdős Problem 1180

*Reference:* [erdosproblems.com/1180](https://www.erdosproblems.com/1180)
-/

namespace Erdos1180

/-- Modular inverses of the integers $1\leq n\leq p^\varepsilon$, as residues modulo $p$. -/
def smallInverseResidues (p : ℕ) (ε : ℝ) : Set (ZMod p) :=
  { x | ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ IsUnit (n : ZMod p) ∧ x = (n : ZMod p)⁻¹ }

/--
Let $\epsilon>0$. Does there exist a constant $C_\epsilon$ such that, for all primes $p$, every
residue modulo $p$ is the sum of at most $C_\epsilon$ many elements of
$$
\{ n^{-1} : 1\leq n\leq p^\epsilon\}
$$
where $n^{-1}$ denotes the inverse of $n$ modulo $p$?
-/
@[category research open, AMS 11]
theorem erdos_1180 :
    answer(sorry) ↔
      ∀ ε > (0 : ℝ), ∃ C : ℕ, ∀ p : ℕ, p.Prime →
        ∀ a : ZMod p, ∃ s : Finset (ZMod p),
          s.card ≤ C ∧ (↑s : Set (ZMod p)) ⊆ smallInverseResidues p ε ∧ ∑ x ∈ s, x = a := by
  sorry

end Erdos1180

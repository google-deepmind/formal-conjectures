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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 540

*References:*
- [erdosproblems.com/540](https://www.erdosproblems.com/540)
- [ErHe64] Erdős, P. and Heilbronn, H., *On the addition of residue classes
  mod $p$*. Acta Arith. (1964), 149--159.
- [Sz70] Szemerédi, E., *On a conjecture of Erdős and Heilbronn*. Acta Arith.
  (1970), 227-229.
-/

namespace Erdos540

/-- A finite set has a non-empty subset whose sum is zero. -/
def HasZeroSubsetSum {G : Type*} [AddCommMonoid G] (A : Finset G) : Prop :=
  ∃ S : Finset G, S ⊆ A ∧ S.Nonempty ∧ S.sum id = 0

/--
Is it true that if $A\subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists
some non-empty $S\subseteq A$ such that $\sum_{n\in S}n\equiv 0\pmod{N}$?

Szemerédi proved the answer is yes, in fact for arbitrary finite abelian groups.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos540.lean"]
theorem erdos_540 : answer(True) ↔
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ A : Finset (ZMod N),
        C * Real.sqrt N ≤ A.card →
          HasZeroSubsetSum A := by
  sorry

end Erdos540

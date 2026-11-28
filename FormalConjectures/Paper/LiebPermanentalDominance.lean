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
# Lieb's permanental dominance conjecture

Elliott H. Lieb proposed Conjecture α in 1966. For matrices of order four, Zeng proved
the inequality for every subgroup and every irreducible character.

*References:*
* [E. H. Lieb, *Proofs of some Conjectures on Permanents*, p. 127](https://iumj.s3-us-west-2.amazonaws.com/abstracts/16008_abs.pdf)
* [I. M. Wanless, *Lieb's permanental dominance conjecture*, Conjecture 1](https://arxiv.org/abs/2202.01867)
* [S. Zeng, *The General Subgroup Permanental-Dominance Conjecture in Order Four*, Theorem 1.1](https://arxiv.org/abs/2608.21749)
* [Open Problems in Numerical Linear Algebra, MI-11](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/matrix-inequalities-and-norms/MI-11)
-/

@[expose] public section

open scoped ComplexOrder

namespace LiebPermanentalDominance

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

/-- Every normalized generalized matrix function agrees with the permanent on diagonal matrices. -/
@[category API, AMS 15 20]
theorem normalized_diagonal (V : FDRep ℂ G) [Nontrivial V] (d : Fin n → ℂ) :
    (Matrix.diagonal d).generalizedMatrixFunction V.character / V.character 1 =
      (Matrix.diagonal d).permanent := by
  have hχ : V.character 1 ≠ 0 := by
    rw [FDRep.char_one]
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  rw [Matrix.generalizedMatrixFunction_diagonal, Matrix.permanent_diagonal, div_eq_iff hχ, mul_comm]

/-- Lieb conjectured that the permanent of a Hermitian positive semidefinite matrix dominates
the normalized generalized matrix function for every subgroup and every nonzero representation.
Both sides are real on these matrices. -/
@[category research open, AMS 15 20]
theorem permanental_dominance (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (G : Subgroup (Equiv.Perm (Fin n))) (V : FDRep ℂ G) [Nontrivial V] :
    A.generalizedMatrixFunction V.character / V.character 1 ≤ A.permanent := by
  sorry

end LiebPermanentalDominance

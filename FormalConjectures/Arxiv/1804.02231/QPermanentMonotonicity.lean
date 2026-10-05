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
# Bapat–Lal q-permanent monotonicity

Conjecture 1 in Section 4 of C. M. da Fonseca, *The mu-permanent revisited*,
https://arxiv.org/abs/1804.02231. Originally formulated by R. B. Bapat and
A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra Appl. 197–198
(1994), 397–409, https://doi.org/10.1016/0024-3795(94)90497-9.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

/-- The number of inversions of a permutation of an ordered finite set. -/
def Equiv.Perm.inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

/-- The q-permanent, with a real deformation parameter and complex values. -/
noncomputable def Matrix.qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (q ^ σ.inversionCount : ℝ) * ∏ i, A i (σ i)

namespace BapatLal

/-- Is the $q$-permanent of every non-diagonal Hermitian positive definite matrix
strictly increasing for $q \in [-1,1]$? The answer is negative. -/
@[category research solved, AMS 15,
    formal_proof using lean4 at "https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/283f0eaf0084a63366da27dd515ce913d7afbcef/lean/Bapat/Main.lean#L25"]
theorem qPermanentMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Icc (-1) 1) := by
  sorry

end BapatLal

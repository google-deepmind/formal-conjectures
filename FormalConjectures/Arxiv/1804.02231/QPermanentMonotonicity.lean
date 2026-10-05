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
# Bapat-Lal q-permanent monotonicity and da Fonseca's extension

Conjectures 1 and 2 in Section 4 of da Fonseca's survey [dF18].
Conjecture 1 originates with Bapat and Lal [BL94]; Conjecture 2 is da Fonseca's
extension to a half-line. The two statements below have negative answers.
Kenta Kitamura's order-144 counterexample has a Lean formalization [Ki26];
the second statement follows by restricting any proposed half-line monotonicity
to $[-1,1]$.

Conjecture 3 in Section 5 of [dF18] was refuted by Matthew J. Colbrook [MI19].
George Stepaniants formalized its negative answer in Lean [St26].
Conjecture 4 in Section 5 is false at $q = 1$, where it specializes to
permanent-on-top, refuted by Shchesnovich [Sh16]. Tran Hoang Anh [Tr21] gives
a simpler counterexample. These are related solved results.

*References:*
- [BL94] R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*,
  Linear Algebra Appl. 197–198 (1994), 397–409,
  https://doi.org/10.1016/0024-3795(94)90497-9.
- [dF18] C. M. da Fonseca, *The mu-permanent revisited*,
  [arXiv:1804.02231](https://arxiv.org/abs/1804.02231) (2018),
  Section 4, Conjectures 1–2; Section 5, Conjectures 3–4.
- [Ki26] Kenta Kitamura, *bapat-lal-q-permanent-lean*, Lean 4 formalization (2026),
  [GitHub repository](https://github.com/KitaKen1/bapat-lal-q-permanent-lean).
- [MI19] *Open Problems in Numerical Linear Algebra*,
  [MI-19: A q-permanent inequality for subset-preserving permutations](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-19/README.md).
  Records Colbrook's mathematical counterexample and Stepaniants' Lean proof (2026).
- [St26] G. Stepaniants, *Lean formalization of MI-19* (2026),
  theorem `NLA.MI19.not_subsetConjecture`, proof revision `cd44ce9`:
  [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean).
- [Sh16] V. S. Shchesnovich, *The permanent-on-top conjecture is false*,
  Linear Algebra Appl. 490 (2016), 196–201,
  https://doi.org/10.1016/j.laa.2015.10.034.
- [Tr21] Tran Hoang Anh, *A simple counterexample for the permanent-on-top conjecture*,
  [arXiv:2101.03428](https://arxiv.org/abs/2101.03428) (2021), Section 4.
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

/-- Conjecture 1 in [dF18, Section 4]: is the $q$-permanent of every
non-diagonal Hermitian positive definite matrix
strictly increasing for $q \in [-1,1]$? The answer is negative [Ki26]. -/
@[category research solved, AMS 15,
    formal_proof using lean4 at "https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/Main.lean#L25"]
theorem qPermanentMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Icc (-1) 1) := by
  sorry

/-- Conjecture 2 in [dF18, Section 4]: does every Hermitian positive definite matrix
have some $ε < -1$ on whose half-line $(ε, ∞)$ its q-permanent is strictly increasing?
The answer is negative [Ki26], by the same counterexample as Conjecture 1. -/
@[category research solved, AMS 15,
    formal_proof using lean4 at "https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/DaFonseca.lean#L18"]
theorem qPermanentHalfLineMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef →
          ∃ ε : ℝ, ε < -1 ∧
            StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Ioi ε) := by
  sorry

end BapatLal

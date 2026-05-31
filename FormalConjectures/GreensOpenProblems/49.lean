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
# Green's Open Problem 49

Also known as the *Marton's conjecture* or the *Polynomial Freiman-Ruzsa conjecture (PFR)*.

*References:*
- [Gr24] [Ben Green's 100 Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.49)
- [Aa19] Aaronson, James. "A counterexample to a strong variant of the Polynomial Freiman-Ruzsa conjecture." arXiv preprint arXiv:1902.00353 (2019).
- [Fa00] I. Farah, Approximate homomorphisms. II. Group homomorphisms, Combinatorica 20 (2000), no. 1, 47–60.
- [GGM25] W. T. Gowers, B. J. Green, F. Manners and T. C. Tao, On a conjecture of Marton, Ann. of Math. (2) 201 (2025), no. 2, 515–549.
- [Gr05] B. J. Green, Finite field models in additive combinatorics, Surveys in combinatorics 2005, 1–27, London Math. Soc. Lecture Note Ser., 327, Cambridge Univ. Press, Cambridge, 2005.
- [GrTa10] B. J. Green and T. C. Tao An equivalence between inverse sumset theorems and inverse conjectures for the U3 norm, Math. Proc. Cambridge Philos. Soc. 149 (2010), no. 1, 1–19.
- [Lo12] S. Lovett, Equivalence of polynomial conjectures in additive combinatorics, Combinatorica 32 (2012), no. 5, 607–618.
- [LoRe17] S. Lovett and O. Regev, A counterexample to a strong variant of the Polynomial Freiman Ruzsa conjecture in Euclidean space, Discrete Anal.(2017), Paper No. 8, 6 pp.
- [Ma19] F. R. W. M. Manners, Formulations of the PFR conjecture over Z, Math. Proc. Cambridge Philos. Soc. 166 (2019), no. 2, 243–245.
- [Sa12] T. Sanders, On the Bogolyubov-Ruzsa lemma, Anal. PDE 5 (2012), no. 3, 627–655.
- [Ta08] T. C. Tao, A counterexample to a strong polynomial Freiman-Ruzsa conjecture, blog post November 2008, available at http://tinyurl.com/36j6hyxv.
-/

open scoped Pointwise Finset

namespace Green49

/-- The vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set with $|A + A| \leq K|A|$. Is it true that $A$
is covered by $K^{O(1)}$ translates of a subspace of size $\leq |A|$?

Solved by [GGM25].
-/
@[category research solved, AMS 5 11]
theorem green_49 : answer(True) ↔
    ∃ C > 0,
      ∀ n (A : Finset (𝔽₂ n)), A.Nonempty →
      ∀ K ≥ (1 : ℝ), (#(A + A) : ℝ) ≤ K * #A →
        ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (T : Finset (𝔽₂ n)),
          Nat.card W ≤ #A ∧
          (#T : ℝ) ≤ K ^ C ∧
          (A : Set (𝔽₂ n)) ⊆ T + W := by
  sorry

-- TODO(jgd) Formulate the analogue (still open) conjecture for subsets of $\mathbb{Z}$ [Gr24, Problem 49, p.25]
end Green49

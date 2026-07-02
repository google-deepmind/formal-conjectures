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
# Erdős Problem 502

*References:*
- [erdosproblems.com/502](https://www.erdosproblems.com/502)
- [BBS83] Bannai, Eiichi and Bannai, Etsuko and Stanton, Dennis, *An upper bound for the
  cardinality of an $s$-distance subset in real Euclidean space. II*. Combinatorica (1983),
  147-152.
- [PePo21] Petrov, Fedor and Pohoata, Cosmin, *A remark on sets with few distances in
  $\mathbb{R}^d$*. Proc. Amer. Math. Soc. (2021), 569-571.
-/

open scoped EuclideanGeometry

namespace Erdos502

/--
What is the size of the largest $A\subseteq \mathbb{R}^n$ such that there are only two distinct
distances between elements of $A$? That is,
\[\# \{ \lvert x-y\rvert : x\neq y\in A\} = 2.\]

Asked to Erdős by Coxeter. Bannai, Bannai, and Stanton [BBS83] have proved that
\[\lvert A\rvert \leq \binom{n+2}{2}.\]
A simple proof of this upper bound was given by Petrov and Pohoata [PePo21].

The exact maximum is not known in general: a lower bound of $\binom{n+1}{2}$ follows from the
construction of Alweiss (see [503]). We formalise the Bannai–Bannai–Stanton upper bound, which
is the content of the linked formal proof: any finite $A\subseteq\mathbb{R}^n$ whose elements
determine exactly two distinct distances satisfies $\lvert A\rvert \leq \binom{n+2}{2}$.
-/
-- Divergences from the hosted proofs: plby's `bannai_bannai_stanton` is stated for general
-- `s`-distance sets with a `Fintype A` instance and `Fintype.card`; we specialise to `s = 2`
-- and use `Set.Finite`/`Set.ncard` per house style, inlining the two-distance-set predicate.
@[category research solved, AMS 51 52,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos502.lean"]
theorem erdos_502 (n : ℕ) (A : Set (ℝ^n)) (hA : A.Finite)
    (hA2 : {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = d}.ncard = 2) :
    A.ncard ≤ (n + 2).choose 2 := by
  sorry

end Erdos502

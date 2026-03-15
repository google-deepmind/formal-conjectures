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
# Erdős Problem 1160

*Reference:* [erdosproblems.com/1160](https://www.erdosproblems.com/1160)

If $g(n)$ denotes the number of groups of order $n$, then $g(n) \le g(2^m)$ for all $n \le 2^m$.

[Va99] Vaughan, R.C., _Problems in combinatorial number theory_, 1999.

[BNV07] Blackburn, S.R., Neumann, P.M. and Venkataraman, G., _Enumeration of finite groups_,
Cambridge Tracts in Mathematics, 2007, xii+281 pp.

[Pa03] Pantelidakis, I., _On the Number of Non-isomorphic Groups of the Same Order_,
DPhil Thesis, University of Oxford, 2003.
-/

open Classical

namespace Erdos1160

/-- Two group structures on the same type are isomorphic if there exists
a multiplicative equivalence between them. -/
def GroupStructIso (n : ℕ) (G₁ G₂ : Group (Fin n)) : Prop :=
  Nonempty (@MulEquiv (Fin n) (Fin n) G₁.toMul G₂.toMul)

/-- Group isomorphism is an equivalence relation on group structures on $\operatorname{Fin}(n)$. -/
instance groupStructSetoid (n : ℕ) : Setoid (Group (Fin n)) where
  r := GroupStructIso n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨@MulEquiv.refl (Fin n) G.toMul⟩
    · intro G₁ G₂ ⟨e⟩
      exact ⟨@MulEquiv.symm (Fin n) (Fin n) G₁.toMul G₂.toMul e⟩
    · intro G₁ G₂ G₃ ⟨e₁⟩ ⟨e₂⟩
      exact ⟨@MulEquiv.trans (Fin n) (Fin n) (Fin n) G₁.toMul G₂.toMul G₃.toMul e₁ e₂⟩

/-- The number of isomorphism classes of groups of order $n$ (OEIS A000001).
Defined as the cardinality of group structures on $\operatorname{Fin}(n)$ modulo isomorphism. -/
noncomputable def numGroupsOfOrder (n : ℕ) : ℕ :=
  Nat.card (Quotient (groupStructSetoid n))

/--
Erdős Problem 1160 [Va99, 5.71]:

Let $g(n)$ denote the number of groups of order $n$. If $n \le 2^m$ then $g(n) \le g(2^m)$.

This conjecture states that among all $n \le 2^m$, the value $g(n)$ is maximized
at $n = 2^m$ (i.e., powers of 2 have the most groups of any order up to that
point). Listed as Question 22.16 in [BNV07], attributed to Erdős and Higman.
-/
@[category research open, AMS 20]
theorem erdos_1160 (n m : ℕ) (h : n ≤ 2 ^ m) :
    numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) := by
  sorry

/--
A stronger variant of Erdős Problem 1160, listed as Question 22.18 in [BNV07]:

The sum $\sum_{n < 2^m} g(n) \le g(2^m)$ for all sufficiently large $m$ (perhaps $m \ge 7$).

This asserts that $g(2^m)$ dominates not just each individual $g(n)$ for $n \le 2^m$,
but the entire sum of all $g(n)$ for $n < 2^m$.
-/
@[category research open, AMS 20]
theorem erdos_1160_sum_variant (m : ℕ) :
    ∑ n ∈ Finset.range (2 ^ m), numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) := by
  sorry

end Erdos1160

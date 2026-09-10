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
# Generic and maximal rank of 3-tensors

The rank of a tensor $T \in \mathbb{C}^{m_1} \otimes \mathbb{C}^{m_2} \otimes \mathbb{C}^{m_3}$ is
the least $r$ such that $T$ is a sum of $r$ decomposable tensors $a \otimes b \otimes c$. Mathlib
records such a tensor as a `Holor ℂ [m₁, m₂, m₃]` and its rank as `Holor.cprank`.

Two basic invariants of the format $(m_1, m_2, m_3)$ are the *generic rank*
$\operatorname{grank}(m_1, m_2, m_3)$, the rank of a generic tensor, and the *maximal rank*
$\operatorname{mrank}(m_1, m_2, m_3)$, the largest rank attained by a tensor of that format.

When $m_3 \geq (m_1-1)(m_2-1) + 1$ the format is called *unbalanced*, and there the generic rank
is $\min(m_3, m_1m_2)$. In the balanced range a dimension count predicts
$\operatorname{grank}(m_1, m_2, m_3) = \lceil m_1m_2m_3 / (m_1 + m_2 + m_3 - 2) \rceil$. This is
known in several families, and the formats $(3, 2p+1, 2p+1)$ are the only balanced formats known
to exceed it. Friedland's Conjecture 5.1, stated here as `isGenericRank_of_balanced`, asserts that
there are no others. The maximal rank is harder: it is known for the formats $2 \times m \times n$
and $(3, 3, 3)$, but no formula is known even for $(n, n, n)$.

*References:*
* [arxiv/0805.3777](https://arxiv.org/abs/0805.3777) S. Friedland, *On the generic and typical
  ranks of 3-tensors*, Linear Algebra Appl. 436 (2012), 478–497. Section 5 collects the known
  values quoted below and states Conjecture 5.1.
* [CGG02] M. V. Catalisano, A. V. Geramita, A. Gimigliano, *Ranks of tensors, secant varieties of
  Segre varieties and fat points*, Linear Algebra Appl. 355 (2002), 263–285. Used for
  `isGenericRank_of_unbalanced`.
* [Str83] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra Appl.
  52/53 (1983), 645–685. Used for `isGenericRank_three_even` and `isGenericRank_three_odd`.
* [Lic85] T. Lickteig, *Typical tensorial rank*, Linear Algebra Appl. 69 (1985), 95–120, and
  H. Abo, G. Ottaviani, C. Peterson, *Induction for secant varieties of Segre varieties*, Trans.
  Amer. Math. Soc. 361 (2009), 767–792, Theorem 5.3. Used for `isGenericRank_cube`.
* [Kru89] J. B. Kruskal, *Rank, decomposition, and uniqueness for 3-way and N-way arrays*, in
  Multiway Data Analysis, North-Holland (1989), 7–18, and J. JáJá, *Optimal evaluation of a pair
  of bilinear forms*, SIAM J. Comput. 8 (1979), 443–462. Used for `isMaxRank_two`.
* [SMS10] T. Sumi, M. Miyazaki, T. Sakata, *About the maximal rank of 3-tensors over the real and
  the complex number field*, Ann. Inst. Statist. Math. 62 (2010), 807–822
  ([arxiv/0806.4048](https://arxiv.org/abs/0806.4048)). Proves the bound of M. D. Atkinson and
  N. M. Stephens, *On the maximal multiplicative complexity of a family of bilinear forms*, Linear
  Algebra Appl. 27 (1979), 1–8, stated there as Theorem 4.1 and proved as Theorem 4.5. Used for
  `cprank_le_of_three_slices` and `isMaxRank_three`.
* [BT15] G. Blekherman, Z. Teitler, *On maximum, typical and generic ranks*, Math. Ann. 362
  (2015), 1021–1031 ([arxiv/1402.2371](https://arxiv.org/abs/1402.2371)), Theorem 1. Used for
  `isMaxRank_le_two_mul_isGenericRank`.
-/

namespace Arxiv.«0805.3777»

/-- The space of complex tensors of a fixed format, topologised as the finite dimensional complex
vector space that it is. -/
noncomputable local instance instTopologicalSpaceHolor {ds : List ℕ} :
    TopologicalSpace (Holor ℂ ds) :=
  inferInstanceAs <| TopologicalSpace (HolorIndex ds → ℂ)

/--
`IsGenericRank ds r` says that `r` is the generic rank of complex tensors of format `ds`, i.e.
that the tensors of rank exactly `r` are dense.

Over `ℂ` exactly one `r` has this property. Write `σ s` for the Zariski closure of the tensors of
rank at most `s`. If `r` is the generic rank then the tensors of rank at most `r` contain a
nonempty Zariski open set `U`, and `U \ σ (r - 1)` is a dense open set of tensors of rank exactly
`r`. For `r' < r` the tensors of rank `r'` lie in the proper closed subvariety `σ r'`, and for
`r' > r` they lie in the complement of `U`.
-/
def IsGenericRank (ds : List ℕ) (r : ℕ) : Prop :=
  Dense {T : Holor ℂ ds | T.cprank = r}

/--
`IsMaxRank ds r` says that `r` is the maximal rank of a complex tensor of format `ds`: every such
tensor has rank at most `r`, and some tensor has rank `r`.
-/
def IsMaxRank (ds : List ℕ) (r : ℕ) : Prop :=
  IsGreatest (Set.range fun T : Holor ℂ ds => T.cprank) r

/-- The maximal rank of a tensor of format `ds` is at most `ds.prod`. -/
@[category API, AMS 15]
theorem IsMaxRank.le_prod {ds : List ℕ} {r : ℕ} (hr : IsMaxRank ds r) : r ≤ ds.prod := by
  obtain ⟨T, hT⟩ := hr.1
  exact hT ▸ Holor.cprank_upper_bound T

/-- The generic rank is at most the maximal rank [Friedland, (4.3)]. -/
@[category API, AMS 15]
theorem IsGenericRank.le_of_isMaxRank {ds : List ℕ} {r R : ℕ} (hr : IsGenericRank ds r)
    (hR : IsMaxRank ds R) : r ≤ R := by
  obtain ⟨T, hT⟩ := hr.nonempty
  exact hT ▸ hR.2 ⟨T, rfl⟩

/-- The generic rank of an $m \times n$ matrix is $\min(m, n)$. This is the case of 2-tensors,
recorded as a check on `IsGenericRank`. -/
@[category textbook, AMS 15]
theorem isGenericRank_matrix (m n : ℕ) : IsGenericRank [m, n] (min m n) := by
  sorry

/--
If $m_3$ is large compared to $m_1$ and $m_2$, a generic tensor of format $(m_1, m_2, m_3)$ has
rank $\min(m_3, m_1m_2)$ [Friedland, (5.1)].
-/
@[category research solved, AMS 14 15]
theorem isGenericRank_of_unbalanced {m₁ m₂ m₃ : ℕ} (h₁ : 1 ≤ m₁) (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃)
    (h : (m₁ - 1) * (m₂ - 1) + 1 ≤ m₃) :
    IsGenericRank [m₁, m₂, m₃] (min m₃ (m₁ * m₂)) := by
  sorry

/-- The generic rank of a $3 \times 2p \times 2p$ tensor is
$\lceil 12p^2 / (4p + 1) \rceil$, the value predicted by a dimension count
[Friedland, (5.3)]. -/
@[category research solved, AMS 14 15]
theorem isGenericRank_three_even {p : ℕ} (hp : 2 ≤ p) :
    IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)) := by
  sorry

/--
The generic rank of a $3 \times (2p+1) \times (2p+1)$ tensor is
$\lceil 3(2p+1)^2 / (4p + 3) \rceil + 1$ [Friedland, (5.4)]. These are the only balanced formats
known to exceed the value predicted by a dimension count. The case $p = 1$ says that the generic
rank of a $3 \times 3 \times 3$ tensor is `5`, not `4`.
-/
@[category research solved, AMS 14 15]
theorem isGenericRank_three_odd {p : ℕ} (hp : 1 ≤ p) :
    IsGenericRank [3, 2 * p + 1, 2 * p + 1] (3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) + 1) := by
  sorry

/-- For $n \neq 3$ the generic rank of an $n \times n \times n$ tensor is
$\lceil n^3 / (3n - 2) \rceil$ [Friedland, (5.8)]. -/
@[category research solved, AMS 14 15]
theorem isGenericRank_cube {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≠ 3) :
    IsGenericRank [n, n, n] (n ^ 3 ⌈/⌉ (3 * n - 2)) := by
  sorry

/--
**Friedland's conjecture.** In the balanced range $m_3 \leq (m_1 - 1)(m_2 - 1)$, and away from the
exceptional formats $(3, 2p+1, 2p+1)$, the generic rank of a tensor of format $(m_1, m_2, m_3)$ is
$\lceil m_1m_2m_3 / (m_1 + m_2 + m_3 - 2) \rceil$, the value predicted by a dimension count
[Friedland, Conjecture 5.1]. It has been verified numerically for $m_3 \leq 14$.
-/
@[category research open, AMS 14 15]
theorem isGenericRank_of_balanced {m₁ m₂ m₃ : ℕ} (h₁ : 3 ≤ m₁) (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃)
    (h : m₃ ≤ (m₁ - 1) * (m₂ - 1)) (hexc : ∀ p : ℕ, (m₁, m₂, m₃) ≠ (3, 2 * p + 1, 2 * p + 1)) :
    IsGenericRank [m₁, m₂, m₃] (m₁ * m₂ * m₃ ⌈/⌉ (m₁ + m₂ + m₃ - 2)) := by
  sorry

/-- The maximal rank of a $2 \times m \times n$ tensor is $m + \min(m, \lfloor n/2 \rfloor)$
[Friedland, (5.13)]. -/
@[category research solved, AMS 15]
theorem isMaxRank_two {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    IsMaxRank [2, m, n] (m + min m (n / 2)) := by
  sorry

/-- Every $n \times n \times 3$ tensor has rank at most $2n - 1$ [SMS10, Theorem 4.5]. -/
@[category research solved, AMS 15]
theorem cprank_le_of_three_slices {n : ℕ} (hn : 1 ≤ n) (T : Holor ℂ [n, n, 3]) :
    T.cprank ≤ 2 * n - 1 := by
  sorry

/-- The maximal rank of a $3 \times 3 \times 3$ tensor is `5` [Friedland, (5.14)]. The upper bound
is [SMS10, Proposition 4.9(1)], a special case of `cprank_le_of_three_slices`; the lower bound is
the generic rank `isGenericRank_three_odd` at $p = 1$. -/
@[category research solved, AMS 15]
theorem isMaxRank_three : IsMaxRank [3, 3, 3] 5 := by
  sorry

/-- The maximal rank is at most twice the generic rank [BT15, Theorem 1]. -/
@[category research solved, AMS 14 15]
theorem isMaxRank_le_two_mul_isGenericRank {ds : List ℕ} {r R : ℕ} (hds : ∀ d ∈ ds, 0 < d)
    (hr : IsGenericRank ds r) (hR : IsMaxRank ds R) : R ≤ 2 * r := by
  sorry

/--
**Open problem.** Determine the maximal rank of a complex $n \times n \times n$ tensor. No formula
is known; for $n = 1, 2, 3$ the values are `1`, `3` and `5`.
-/
@[category research open, AMS 15]
theorem isMaxRank_cube (n : ℕ) : IsMaxRank [n, n, n] ((answer(sorry) : ℕ → ℕ) n) := by
  sorry

end Arxiv.«0805.3777»

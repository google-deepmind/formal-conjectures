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

Counting parameters gives the lower bound
$\operatorname{grank}(m_1, m_2, m_3) \geq r_0(m_1, m_2, m_3) :=
\lceil m_1m_2m_3 / (m_1 + m_2 + m_3 - 2) \rceil$. Once $m_3$ exceeds $(m_1-1)(m_2-1)$ the generic
rank is known to be $\min(m_3, m_1m_2)$, so the interesting case is the *critical range*
$3 \leq m_1 \leq m_2 \leq m_3 \leq (m_1-1)(m_2-1)$ [Fri12, Conjecture 5.1; BFZ24, (4.14)]. There
the bound $r_0$ is attained in every case that has been settled, except for the formats
$(3, 2p+1, 2p+1)$, where the generic rank is $r_0 + 1$. Friedland's conjecture, stated here as
`isGenericRank_of_le_critical`, is that these are the only exceptions.

The maximal rank is much less well understood. It is known for the formats
$2 \times m \times n$ and for a range of small formats, but no formula is known even for
$(n, n, n)$, and $\operatorname{mrank}(3, 3, 5)$ is undetermined.

Tensor rank is invariant under permuting the three factors, but `Holor ℂ [m₁, m₂, m₃]` and its
permutations are different types and Mathlib has no transport lemma between them. Each statement
below therefore writes the format in the order its own source uses.

*References:*
* [Fri12] S. Friedland, *On the generic and typical ranks of 3-tensors*, Linear Algebra Appl. 436
  (2012), 478-497, https://doi.org/10.1016/j.laa.2011.05.008
  ([arxiv/0805.3777](https://arxiv.org/abs/0805.3777)). Conjecture 5.1, and the survey of known
  values in Section 5.
* [BFZ24] W. Bruzda, S. Friedland, K. Życzkowski, *Rank of a tensor and quantum entanglement*,
  Linear Multilinear Algebra 72 (2024), 1796-1859,
  https://doi.org/10.1080/03081087.2023.2211717
  ([arxiv/1912.06854](https://arxiv.org/abs/1912.06854)). A survey; the numbering used below is
  that of the arXiv version. Conjecture 4.12 restates [Fri12, Conjecture 5.1], and Sections 4.5
  and 4.6 collect the current status.
* [CGG02] M. V. Catalisano, A. V. Geramita, A. Gimigliano, *Ranks of tensors, secant varieties of
  Segre varieties and fat points*, Linear Algebra Appl. 355 (2002), 263-285,
  https://doi.org/10.1016/S0024-3795(02)00352-X. Used for `isGenericRank_of_gt_critical`.
* [Str83] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra Appl.
  52/53 (1983), 645-685, https://doi.org/10.1016/0024-3795(83)80041-X. Used for
  `isGenericRank_three_even` and `isGenericRank_three_odd`.
* [AOP09] H. Abo, G. Ottaviani, C. Peterson, *Induction for secant varieties of Segre varieties*,
  Trans. Amer. Math. Soc. 361 (2009), 767-792, https://doi.org/10.1090/S0002-9947-08-04725-9.
  Used for `isGenericRank_four`.
* [Lic85] T. Lickteig, *Typical tensorial rank*, Linear Algebra Appl. 69 (1985), 95-120,
  https://doi.org/10.1016/0024-3795(85)90070-9. Used for `isGenericRank_cube`.
* [AS79] M. D. Atkinson, N. M. Stephens, *On the maximal multiplicative complexity of a family of
  bilinear forms*, Linear Algebra Appl. 27 (1979), 1-8,
  https://doi.org/10.1016/0024-3795(79)90026-0. Used for `isMaxRank_two`,
  `cprank_le_of_three_slices`, `isMaxRank_of_le_min` and `isMaxRank_three_three_five_bounds`.
* [JaJa79] J. JáJá, *Optimal evaluation of pairs of bilinear forms*, SIAM J. Comput. 8 (1979),
  443-462, https://doi.org/10.1137/0208037, and J. B. Kruskal, *Rank, decomposition, and
  uniqueness for 3-way and N-way arrays*, in Multiway Data Analysis, North-Holland (1989), 7-18.
  Cited by [Fri12] for `isMaxRank_two`.
* [SMS10] T. Sumi, M. Miyazaki, T. Sakata, *About the maximal rank of 3-tensors over the real and
  the complex number field*, Ann. Inst. Statist. Math. 62 (2010), 807-822,
  https://doi.org/10.1007/s10463-010-0294-5 ([arxiv/0806.4048](https://arxiv.org/abs/0806.4048)).
  Theorem 4.5 proves the first of the two bounds that [AS79] states without proof; Proposition
  4.9(1) is the special case used for `isMaxRank_three`.
* [BT15] G. Blekherman, Z. Teitler, *On maximum, typical and generic ranks*, Math. Ann. 362
  (2015), 1021-1031, https://doi.org/10.1007/s00208-014-1150-3
  ([arxiv/1402.2371](https://arxiv.org/abs/1402.2371)), Theorem 1. Used for
  `isMaxRank_le_two_mul_isGenericRank`.
-/

namespace Arxiv.«0805.3777»

/-- The space of complex tensors of a fixed format, topologised as the finite-dimensional complex
vector space that it is. -/
noncomputable scoped instance instTopologicalSpaceHolor {ds : List ℕ} :
    TopologicalSpace (Holor ℂ ds) :=
  inferInstanceAs <| TopologicalSpace (HolorIndex ds → ℂ)

/--
`IsGenericRank ds r` says that `r` is the generic rank of complex tensors of format `ds`: the
tensors of rank `r` contain a dense open set.

This is the form the sources establish: the tensors of rank other than the generic rank lie in a
proper algebraic subset [Fri12, Theorem 3.4]. It determines `r` uniquely, by
`IsGenericRank.unique`.
-/
def IsGenericRank (ds : List ℕ) (r : ℕ) : Prop :=
  ∃ U : Set (Holor ℂ ds), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank = r

/--
`IsMaxRank ds r` says that `r` is the maximal rank of a complex tensor of format `ds`: every such
tensor has rank at most `r`, and some tensor has rank `r`.
-/
def IsMaxRank (ds : List ℕ) (r : ℕ) : Prop :=
  IsGreatest (Set.range fun T : Holor ℂ ds => T.cprank) r

/-- A tensor has rank `0` exactly when it is zero. -/
@[category API, AMS 15]
theorem cprank_eq_zero_iff {ds : List ℕ} (T : Holor ℂ ds) : T.cprank = 0 ↔ T = 0 := by
  classical
  constructor
  · intro h
    have h0 : Holor.CPRankMax 0 T := by
      unfold Holor.cprank at h
      have hspec := Nat.find_spec (p := fun n => Holor.CPRankMax n T)
        (H := ⟨ds.prod, Holor.cprankMax_upper_bound T⟩)
      rwa [show (Nat.find _ : ℕ) = 0 from h] at hspec
    cases h0 with
    | zero => rfl
  · rintro rfl
    have : (0 : Holor ℂ ds).cprank ≤ 0 := by
      unfold Holor.cprank
      exact Nat.find_min' _ Holor.CPRankMax.zero
    omega

/-- The maximal rank of a tensor of format `ds` is at most `ds.prod`. -/
@[category API, AMS 15]
theorem IsMaxRank.le_prod {ds : List ℕ} {r : ℕ} (hr : IsMaxRank ds r) : r ≤ ds.prod := by
  obtain ⟨T, hT⟩ := hr.1
  exact hT ▸ Holor.cprank_upper_bound T

/-- There is at most one generic rank. -/
@[category API, AMS 15]
theorem IsGenericRank.unique {ds : List ℕ} {r r' : ℕ} (hr : IsGenericRank ds r)
    (hr' : IsGenericRank ds r') : r = r' := by
  obtain ⟨U, hU, hUd, hUr⟩ := hr
  obtain ⟨V, hV, hVd, hVr⟩ := hr'
  obtain ⟨T, hTU, hTV⟩ := hVd.inter_open_nonempty U hU hUd.nonempty
  rw [← hUr T hTU, hVr T hTV]

/-- The generic rank is at most the maximal rank [Fri12, (4.3)]. -/
@[category API, AMS 15]
theorem IsGenericRank.le_of_isMaxRank {ds : List ℕ} {r R : ℕ} (hr : IsGenericRank ds r)
    (hR : IsMaxRank ds R) : r ≤ R := by
  obtain ⟨U, hU, hUd, hUr⟩ := hr
  obtain ⟨T, hT⟩ := hUd.nonempty
  exact hUr T hT ▸ hR.2 ⟨T, rfl⟩

/-- The maximal rank of a $1 \times 1 \times 1$ tensor is `1`. -/
@[category test, AMS 15]
theorem isMaxRank_one : IsMaxRank [1, 1, 1] 1 := by
  set S : Holor ℂ [1, 1, 1] := fun _ => 1 with hS
  refine ⟨⟨S, ?_⟩, ?_⟩
  · show S.cprank = 1
    have hle : S.cprank ≤ 1 := by simpa using Holor.cprank_upper_bound S
    have hne : S.cprank ≠ 0 := by
      rw [Ne, cprank_eq_zero_iff]
      intro h
      exact one_ne_zero (congrFun h ⟨[0, 0, 0], by simp⟩)
    omega
  · rintro y ⟨T, rfl⟩
    simpa using Holor.cprank_upper_bound T

/-- The generic rank of an $m \times n$ matrix is $\min(m, n)$: the 2-tensor case. -/
@[category textbook, AMS 15]
theorem isGenericRank_matrix (m n : ℕ) : IsGenericRank [m, n] (min m n) := by
  sorry

/--
Above the critical range, a generic tensor of format $(m_1, m_2, m_3)$ has rank
$\min(m_3, m_1m_2)$ [Fri12, (5.1)].
-/
@[category research solved, AMS 14 15]
theorem isGenericRank_of_gt_critical {m₁ m₂ m₃ : ℕ} (h₁ : 1 ≤ m₁) (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃)
    (h : (m₁ - 1) * (m₂ - 1) < m₃) :
    IsGenericRank [m₁, m₂, m₃] (min m₃ (m₁ * m₂)) := by
  sorry

/-- The generic rank of a $3 \times 2p \times 2p$ tensor is $\lceil 12p^2 / (4p + 1) \rceil$, the
value $r_0$ predicted by a dimension count [Fri12, (5.3)]. The hypothesis $2 \leq p$ is the
ordering $3 \leq 2p$ of the format. -/
@[category research solved, AMS 14 15]
theorem isGenericRank_three_even {p : ℕ} (hp : 2 ≤ p) :
    IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)) := by
  sorry

/--
The generic rank of a $3 \times (2p+1) \times (2p+1)$ tensor is
$\lceil 3(2p+1)^2 / (4p + 3) \rceil + 1$, one more than the value $r_0$ predicted by a dimension
count [Fri12, (5.4)]. These are the only formats in the critical range known to exceed $r_0$. The
case $p = 1$ says that the generic rank of a $3 \times 3 \times 3$ tensor is `5`, not `4`.
-/
@[category research solved, AMS 14 15]
theorem isGenericRank_three_odd {p : ℕ} (hp : 1 ≤ p) :
    IsGenericRank [3, 2 * p + 1, 2 * p + 1] (3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) + 1) := by
  sorry

/-- The generic rank of a $4 \times m \times m$ tensor is $\lceil 4m^2 / (2m + 2) \rceil$
[Fri12, (5.7)]. This is the case $(4, m, m)$ of `isGenericRank_of_le_critical`, settled in
[AOP09]; see [BFZ24, Section 4.5]. -/
@[category research solved, AMS 14 15]
theorem isGenericRank_four {m : ℕ} (hm : 3 ≤ m) :
    IsGenericRank [4, m, m] (4 * m ^ 2 ⌈/⌉ (2 * m + 2)) := by
  sorry

/-- For $n \neq 3$ the generic rank of an $n \times n \times n$ tensor is
$\lceil n^3 / (3n - 2) \rceil$ [Fri12, (5.8)]. -/
@[category research solved, AMS 14 15]
theorem isGenericRank_cube {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≠ 3) :
    IsGenericRank [n, n, n] (n ^ 3 ⌈/⌉ (3 * n - 2)) := by
  sorry

/--
**Friedland's conjecture.** In the critical range $m_3 \leq (m_1 - 1)(m_2 - 1)$, and away from the
formats $(3, 2p+1, 2p+1)$, the generic rank of a tensor of format $(m_1, m_2, m_3)$ is the value
$\lceil m_1m_2m_3 / (m_1 + m_2 + m_3 - 2) \rceil$ predicted by a dimension count
[Fri12, Conjecture 5.1]. It is known for $m_1 \leq 4$ and for $(n, n, n)$, and has been verified
numerically throughout the critical range for $m_3 \leq 20$ [BFZ24, Section 4.5].
-/
@[category research open, AMS 14 15]
theorem isGenericRank_of_le_critical {m₁ m₂ m₃ : ℕ} (h₁ : 3 ≤ m₁) (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃)
    (h : m₃ ≤ (m₁ - 1) * (m₂ - 1)) (hexc : ∀ p : ℕ, (m₁, m₂, m₃) ≠ (3, 2 * p + 1, 2 * p + 1)) :
    IsGenericRank [m₁, m₂, m₃] (m₁ * m₂ * m₃ ⌈/⌉ (m₁ + m₂ + m₃ - 2)) := by
  sorry

/-- The maximal rank of a $2 \times m \times n$ tensor is $m + \min(m, \lfloor n/2 \rfloor)$
[Fri12, (5.13)]; equivalently [BFZ24, (4.9)]. -/
@[category research solved, AMS 15]
theorem isMaxRank_two {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    IsMaxRank [2, m, n] (m + min m (n / 2)) := by
  sorry

/-- Every $n \times n \times 3$ tensor has rank at most $2n - 1$ [SMS10, Theorem 4.5]. -/
@[category research solved, AMS 15]
theorem cprank_le_of_three_slices {n : ℕ} (hn : 1 ≤ n) (T : Holor ℂ [n, n, 3]) :
    T.cprank ≤ 2 * n - 1 := by
  sorry

/-- The maximal rank of a $3 \times 3 \times 3$ tensor is `5`. The upper bound is
[SMS10, Proposition 4.9(1)], a special case of `cprank_le_of_three_slices`; the lower bound is the
generic rank `isGenericRank_three_odd` at $p = 1$. -/
@[category research solved, AMS 14 15]
theorem isMaxRank_three : IsMaxRank [3, 3, 3] 5 := by
  sorry

/-- For $u \leq \min(4, m)$ the maximal rank of an $m \times n \times (mn - u)$ tensor is
$mn - \lceil u/2 \rceil$ [BFZ24, (4.24)]. -/
@[category research solved, AMS 15]
theorem isMaxRank_of_le_min {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    IsMaxRank [m, n, m * n - u] (m * n - u ⌈/⌉ 2) := by
  sorry

/-- The maximal rank of a $3 \times 3 \times 5$ tensor is `6` or `7` [BFZ24, (4.20)]. -/
@[category research solved, AMS 15]
theorem isMaxRank_three_three_five_bounds {R : ℕ} (hR : IsMaxRank [3, 3, 5] R) :
    6 ≤ R ∧ R ≤ 7 := by
  sorry

/-- **Open problem.** Determine the maximal rank of a $3 \times 3 \times 5$ tensor. It is the one
undetermined entry of the table of $\operatorname{mrank}(3, 3, p)$ for $p \leq 9$
[BFZ24, (4.20)]. -/
@[category research open, AMS 15]
theorem isMaxRank_three_three_five : IsMaxRank [3, 3, 5] answer(sorry) := by
  sorry

/-- The maximal rank is at most twice the generic rank [BT15, Theorem 1]. -/
@[category research solved, AMS 14 15]
theorem isMaxRank_le_two_mul_isGenericRank {ds : List ℕ} {r R : ℕ} (hr : IsGenericRank ds r)
    (hR : IsMaxRank ds R) : R ≤ 2 * r := by
  sorry

/--
**Open problem.** Determine the maximal rank of a complex $n \times n \times n$ tensor. No formula
is known: for $n = 1, 2, 3$ the values are `1`, `3` and `5`, while for $4 \leq n \leq 7$ only
bounds such as $\operatorname{mrank}(4, 4, 4) \leq 10$ are available [BFZ24, (4.25)-(4.28)].
-/
@[category research open, AMS 15]
theorem isMaxRank_cube {n : ℕ} (hn : 1 ≤ n) :
    IsMaxRank [n, n, n] ((answer(sorry) : ℕ → ℕ) n) := by
  sorry

end Arxiv.«0805.3777»

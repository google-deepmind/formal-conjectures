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
# Erdős Problem 789

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by
some counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes `answer(sorry)` for an unknown function.

Straus [Str66] proved that $h(n) \ll \sqrt{n}$. Erdős [Er62c] and Choi [Ch74b] proved that
$(n\log(n))^{1/3} \ll h(n)$. Korsky [Ko26] improved this to $h(n) \gg \sqrt{n\log\log n/\log n}$.
The variants record these bounds and the open question whether $h(n) = \Theta(\sqrt{n})$. The file
proves Korsky's bound, following [Ko26], and derives from it the Erdős–Choi bound and
$h(n) \neq O((n\log(n))^{1/3})$.

*References:*
- [erdosproblems.com/789](https://www.erdosproblems.com/789)
- [Str66] Straus, E. G., _On a problem in combinatorial number theory_. J. Math. Sci. (1966), 77--80.
- [Er62c] Erdős, Pál, _Some remarks on number theory_. {III}. Mat. Lapok (1962), 28--38.
- [Ch74b] Choi, S. L. G., _On an extremal problem in number theory_. J. Number Theory (1974), 105--111.
- [Ko26] Korsky, S., _A near-square-root bound for an additive problem of Erdős and Straus_ (2026).
  [Proof claim](https://www.erdosproblems.com/forum/thread/789/proof-claims).
-/

@[expose] public section

open Filter

open scoped Asymptotics Finset

namespace Erdos789

/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)

/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Estimate $h(n)$.
-/
@[category research open, AMS 5]
theorem erdos_789 :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Is $h(n) = \Theta(\sqrt{n})$?
-/
@[category research open, AMS 5]
theorem erdos_789.variants.sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

/-- Straus [Str66] proved that $h(n) \ll \sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.isBigO_sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  sorry

/-- By the solved variant `erdos_789.variants.isBigO_sq`, in order to prove
`erdos_789.variants.sq` it suffices to show $\sqrt{n}=O(h(n))$. -/
@[category research open, AMS 5]
theorem erdos_789.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry

/-! ### Korsky's lower bound

This section proves the bound of Korsky [Ko26]. Call $B \subseteq \mathbb{Z}$ admissible if every
relation $\sum_{b \in B} \varepsilon_b b = 0$ with $\varepsilon_b \in \{-1, 0, 1\}$ has
$\sum_{b \in B} \varepsilon_b = 0$. In an admissible set, equal subset sums have equally many
terms.

Let $D$ be a maximal admissible subset of $A \setminus \{0\}$ and $k = |D| + 1$. As in Lemma 2 of
[Ko26], at least half of $A \setminus \{0\}$ is mapped to nonzero integers of absolute value at
most $k^{2k+2}$, and relations with at most $k$ terms are preserved. Counting $p$-adic valuations
of these integers for primes $p > k$ then bounds $|A|$.

The formalization differs from [Ko26] in two ways. It works with signed relations in
$A \setminus \{0\}$ and does not reduce to positive integers. Instead of Mertens' theorem it uses
Chebyshev's bounds on the blocks $(y, 16y]$.
-/

section Korsky

open Finset

/-! #### Linear algebra -/

/-- Expansion along the first row: the determinant is linear in the first row `u`. -/
@[category API, AMS 15]
private lemma det_cons_row {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (R : Fin r → ι → ℤ) (col : Fin (r + 1) → ι) (u : ι → ℤ) :
    (Matrix.of fun a b => (Fin.cons u R : Fin (r + 1) → ι → ℤ) a (col b)).det =
      ∑ i, u i * (Matrix.of fun a b =>
        (Fin.cons (Pi.single i 1) R : Fin (r + 1) → ι → ℤ) a (col b)).det := by
  simp only [Matrix.det_succ_row_zero, mul_sum]
  refine Eq.trans ?_ sum_comm.symm
  refine sum_congr rfl fun k _ => ?_
  simp [Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]
  ring

/-- Expansion along the first column, summed against `x`. -/
@[category API, AMS 15]
private lemma sum_det_cons_col {ι : Type*} [Fintype ι] {r : ℕ}
    (V : Fin (r + 1) → ι → ℤ) (c : Fin r → ι) (x : ι → ℤ) :
    ∑ j, x j * (Matrix.of fun a b => V a ((Fin.cons j c : Fin (r + 1) → ι) b)).det =
      ∑ a : Fin (r + 1), (-1) ^ (a : ℕ) * (∑ j, V a j * x j) *
        (Matrix.of fun a' b => V (a.succAbove a') (c b)).det := by
  simp only [Matrix.det_succ_column_zero, mul_sum, sum_mul]
  refine sum_comm.trans (sum_congr rfl fun a _ => sum_congr rfl fun j _ => ?_)
  simp [Matrix.submatrix]
  ring

/-- Cramer's rule. Let $W$ be a set of integer vectors indexed by $\iota$, with entries of
absolute value at most $K$. There are integer vectors $z_j$ orthogonal to $W$, with entries of
absolute value at most $(d+1)!\,K^{d+1}$ for $d = |\iota|$, such that $y \cdot z_j \neq 0$ for
some $j$ whenever $y \cdot x \neq 0$ for some $x$ orthogonal to $W$. -/
@[category API, AMS 15]
private lemma exists_kernel_vectors {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Set (ι → ℤ))
    (K : ℤ) (hK : 1 ≤ K) (hW : ∀ w ∈ W, ∀ i, |w i| ≤ K) :
    ∃ z : ι → ι → ℤ, (∀ j, ∀ w ∈ W, ∑ i, w i * z j i = 0) ∧
      (∀ j i, |z j i| ≤ ((Fintype.card ι + 1).factorial : ℤ) * K ^ (Fintype.card ι + 1)) ∧
      ∀ x : ι → ℤ, (∀ w ∈ W, ∑ i, w i * x i = 0) →
        ∀ y : ι → ℤ, ∑ i, y i * x i ≠ 0 → ∃ j, ∑ i, y i * z j i ≠ 0 := by
  classical
  -- `P m`: some `m` vectors of `W` have a nonsingular `m × m` minor.
  let P : ℕ → Prop := fun m => ∃ (R : Fin m → ι → ℤ) (c : Fin m → ι), (∀ a, R a ∈ W) ∧
    (Matrix.of fun a b => R a (c b)).det ≠ 0
  -- A nonsingular minor has distinct columns, so `m ≤ card ι`.
  have hbound : ∀ m, P m → m ≤ Fintype.card ι := by
    rintro m ⟨R, c, -, hdet⟩
    have hc : Function.Injective c := fun a b hab => by
      by_contra hne
      exact hdet (Matrix.det_zero_of_column_eq hne fun k => by simp [hab])
    simpa using Fintype.card_le_of_injective c hc
  -- Take `r` maximal with `P r` (the empty minor has determinant `1`).
  obtain ⟨r, ⟨R, c, hRW, hΔ⟩, hr⟩ : ∃ r, P r ∧ ¬ P (r + 1) :=
    ⟨Nat.findGreatest P (Fintype.card ι),
      Nat.findGreatest_spec (P := P) (Nat.zero_le _) ⟨![], ![], fun a => a.elim0, by simp⟩,
      fun h => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h⟩
  -- The bordered matrix with first row `u` and first column `j`; `z j i` is its determinant
  -- for `u = Pi.single i 1`.
  let M : (ι → ℤ) → ι → Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ := fun u j =>
    Matrix.of fun a b => (Fin.cons u R : Fin (r + 1) → ι → ℤ) a
      ((Fin.cons j c : Fin (r + 1) → ι) b)
  have hlin : ∀ u j, (M u j).det = ∑ i, u i * (M (Pi.single i 1) j).det :=
    fun u j => det_cons_row R _ u
  refine ⟨fun j i => (M (Pi.single i 1) j).det, fun j w hw => ?_, fun j i => ?_,
    fun x hx y hy => ?_⟩
  · -- Orthogonality: by maximality of `r`, the bordered minor with first row `w ∈ W` vanishes.
    rw [← hlin]
    by_contra h
    exact hr ⟨Fin.cons w R, Fin.cons j c,
      fun a => by cases a using Fin.cases <;> simp [hw, hRW], h⟩
  · -- Size: all entries are at most `K`, so `|det| ≤ (r+1)! K^(r+1)` with `r ≤ card ι`.
    have hr' : r ≤ Fintype.card ι := hbound r ⟨R, c, hRW, hΔ⟩
    have hent : ∀ a b, AbsoluteValue.abs (M (Pi.single i 1) j a b) ≤ K := fun a b => by
      cases a using Fin.cases with
      | zero =>
        simp only [M, Matrix.of_apply, Fin.cons_zero, Pi.single_apply, AbsoluteValue.abs_apply]
        split_ifs <;> simp [hK]
        linarith
      | succ a => simpa [M] using hW _ (hRW a) _
    calc |(M (Pi.single i 1) j).det| ≤ (r + 1).factorial • K ^ (r + 1) := by
          simpa using Matrix.det_le hent
      _ ≤ _ := by rw [nsmul_eq_mul]; gcongr
  · -- Detection: `∑ j, x j * det (M y j) = (∑ i, y i * x i) * Δ ≠ 0`, expanding along the
    -- first column; only the first row contributes since `x` is orthogonal to `W`.
    by_contra! h
    have h' : ∀ j, (M y j).det = 0 := fun j => (hlin y j).trans (h j)
    have hxR : ∀ a, ∑ i, R a i * x i = 0 := fun a => hx _ (hRW a)
    have key : ∑ j, x j * (M y j).det =
        (∑ i, y i * x i) * (Matrix.of fun a b => R a (c b)).det := by
      refine (sum_det_cons_col (Fin.cons y R) c x).trans ?_
      rw [Fin.sum_univ_succ]
      simp [hxR]
    simp [h', hy, hΔ] at key

/-! #### Averaging -/

/-- If $w_{j_0} \neq 0$, then at least half of all $S \subseteq \iota$ satisfy
$\sum_{j \in S} w_j \neq 0$: toggling $j_0$ turns a zero sum into a nonzero one. -/
@[category API, AMS 5]
private lemma card_le_two_mul_card_filter_sum_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℤ) {j₀ : ι} (hj₀ : w j₀ ≠ 0) :
    Fintype.card (Finset ι) ≤ 2 * #(univ.filter fun S : Finset ι => ∑ j ∈ S, w j ≠ 0) := by
  -- `f` toggles the membership of `j₀`; it is an involution
  let f : Finset ι → Finset ι := fun S => if j₀ ∈ S then S.erase j₀ else insert j₀ S
  have hf : ∀ S, f (f S) = S := fun S => by
    by_cases h : j₀ ∈ S
    · simp [f, h, insert_erase h]
    · simp [f, h, erase_insert h]
  -- the sums over `S` and `f S` differ by `± w j₀`
  have hfS : ∀ S, ∑ j ∈ S, w j = 0 → ∑ j ∈ f S, w j ≠ 0 := fun S hS => by
    by_cases h : j₀ ∈ S
    · simp [f, h, sum_erase_eq_sub h, hS, hj₀]
    · simp [f, h, sum_insert h, hS, hj₀]
  -- hence every `S` lies in `N` or in the image of `N` under `f`
  set N := univ.filter fun S : Finset ι => ∑ j ∈ S, w j ≠ 0
  have hsub : (univ : Finset (Finset ι)) ⊆ N ∪ N.image f := by
    intro S _
    by_cases hS : ∑ j ∈ S, w j = 0
    · exact mem_union_right _ (mem_image.2 ⟨f S, mem_filter.2 ⟨mem_univ _, hfS S hS⟩, hf S⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hS⟩)
  calc Fintype.card (Finset ι) = #(univ : Finset (Finset ι)) := card_univ.symm
    _ ≤ #(N ∪ N.image f) := card_le_card hsub
    _ ≤ #N + #(N.image f) := card_union_le _ _
    _ ≤ #N + #N := Nat.add_le_add_left card_image_le _
    _ = 2 * #N := (two_mul _).symm

/-- Averaging over $\{0, 1\}$-combinations. If $v_a \neq 0$ for all $a \in P$, then some
$S \subseteq \iota$ has $\sum_{j \in S} v_{a,j} \neq 0$ for at least half of the $a \in P$. -/
@[category API, AMS 5]
private lemma exists_finset_card_le_two_mul {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset α) (v : α → ι → ℤ) (hv : ∀ a ∈ P, ∃ j, v a j ≠ 0) :
    ∃ S : Finset ι, #P ≤ 2 * #(P.filter fun a => ∑ j ∈ S, v a j ≠ 0) := by
  -- double count the pairs `(S, a)` with `∑ j ∈ S, v a j ≠ 0`
  have hsum : ∑ S : Finset ι, #(P.filter fun a => ∑ j ∈ S, v a j ≠ 0) =
      ∑ a ∈ P, #(univ.filter fun S : Finset ι => ∑ j ∈ S, v a j ≠ 0) := by
    simp only [card_filter]
    exact sum_comm
  -- each `a ∈ P` has a nonzero sum for at least half of all `S`
  have hhalf : Fintype.card (Finset ι) * #P ≤
      2 * ∑ S : Finset ι, #(P.filter fun a => ∑ j ∈ S, v a j ≠ 0) :=
    calc Fintype.card (Finset ι) * #P = ∑ _a ∈ P, Fintype.card (Finset ι) := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ P, 2 * #(univ.filter fun S : Finset ι => ∑ j ∈ S, v a j ≠ 0) := by
          refine sum_le_sum fun a ha => ?_
          obtain ⟨j₀, hj₀⟩ := hv a ha
          exact card_le_two_mul_card_filter_sum_ne_zero (v a) hj₀
      _ = 2 * ∑ S : Finset ι, #(P.filter fun a => ∑ j ∈ S, v a j ≠ 0) := by
          rw [hsum, mul_sum]
  -- if every `S` kept less than half of `P`, summing over all `S` would contradict `hhalf`
  by_contra! h
  have hlt := sum_lt_sum_of_nonempty univ_nonempty fun S (_ : S ∈ univ) => h S
  rw [← mul_sum, sum_const, card_univ, smul_eq_mul] at hlt
  exact absurd hhalf (not_le.2 hlt)

/-! #### Chebyshev bounds -/

/-- For large $x$, $\log x \le \sqrt{x}/16$. -/
@[category API, AMS 11]
private lemma exists_log_le_sqrt : ∃ N : ℝ, ∀ x ≥ N, Real.log x ≤ √x / 16 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine ⟨max N 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have := hN x (le_trans (le_max_left _ _) hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at this
  linarith

/-- $\theta(16y) = \theta(y) + \sum_{y < p \le 16y} \log p$. -/
@[category API, AMS 11]
private lemma theta_split (y : ℕ) :
    Chebyshev.theta ((16 * y : ℕ) : ℝ) =
      Chebyshev.theta y + ∑ p ∈ (Ioc y (16 * y)).filter Nat.Prime, Real.log p := by
  simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le y) (by omega)).symm

/-- One block: for large $y$, $\sum_{y < p \le 16y} \log p / p \ge \log 2 / 4$. -/
@[category API, AMS 11]
private lemma block : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
    Real.log 2 / 4 ≤ ∑ p ∈ (Ioc y (16 * y)).filter Nat.Prime, Real.log p / p := by
  obtain ⟨N, hN⟩ := exists_log_le_sqrt
  refine ⟨⌈N⌉₊ + 1, fun y hy => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (le_trans (by omega) hy : 1 ≤ y)
  have hNy : N ≤ y := (Nat.le_ceil N).trans (by exact_mod_cast (le_trans (by omega) hy))
  -- Each term is at least `log p / (16 y)`.
  have hterm : (∑ p ∈ (Ioc y (16 * y)).filter Nat.Prime, Real.log p) / (16 * y) ≤
      ∑ p ∈ (Ioc y (16 * y)).filter Nat.Prime, Real.log p / p := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp'.1)
    have hp16 : (p : ℝ) ≤ 16 * y := by exact_mod_cast hp'.2
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hp0 hp16
  -- Chebyshev's bounds.
  have hθ1 := Chebyshev.theta_ge (16 * y)
  have hθ2 := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) y)
  have hsplit := theta_split y
  push_cast at hθ1 hsplit
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 := Real.log_two_gt_d9
  -- The error terms are small.
  have h1 : Real.log (16 * y) ≤ √(16 * y) / 16 := hN _ (by linarith)
  have h2 : Real.log (16 * y + 1) ≤ √(16 * y + 1) / 16 := hN _ (by linarith)
  have hsq : √(16 * y) * √(16 * y) = 16 * y := Real.mul_self_sqrt (by positivity)
  have hsq' : √(16 * (y : ℝ) + 1) ≤ 16 * y + 1 :=
    (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  have h3 : 2 * √(16 * y) * Real.log (16 * y) ≤ 2 * y := by
    have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (16 * y))
    nlinarith
  set S := ∑ p ∈ (Ioc y (16 * y)).filter Nat.Prime, Real.log p
  have hS : 4 * y * Real.log 2 ≤ S := by nlinarith
  calc Real.log 2 / 4 = 4 * y * Real.log 2 / (16 * y) := by field_simp; ring
    _ ≤ S / (16 * y) := by gcongr
    _ ≤ _ := hterm

/-- For large $k$ and all $J$, $\sum_{k < p \le 16^J k} \log p / p \ge J \log 2 / 4$. This sums
`block` over the blocks $(16^i k, 16^{i+1} k]$ and replaces Mertens' theorem. -/
@[category API, AMS 11]
private lemma exists_sum_log_div_ge : ∃ y₀ : ℕ, ∀ k : ℕ, y₀ ≤ k → ∀ J : ℕ,
    (J : ℝ) * (Real.log 2 / 4) ≤
      ∑ p ∈ (Ioc k (16 ^ J * k)).filter Nat.Prime, Real.log p / p := by
  obtain ⟨y₀, hblock⟩ := block
  refine ⟨y₀, fun k hk J => ?_⟩
  induction J with
  | zero => simp
  | succ J ih =>
    have hle : k ≤ 16 ^ J * k := Nat.le_mul_of_pos_left k (by positivity)
    -- Split off the last block `(16^J k, 16^(J+1) k]`.
    have hsplit : ∑ p ∈ (Ioc k (16 ^ (J + 1) * k)).filter Nat.Prime, Real.log p / p =
        ∑ p ∈ (Ioc k (16 ^ J * k)).filter Nat.Prime, Real.log p / p +
        ∑ p ∈ (Ioc (16 ^ J * k) (16 * (16 ^ J * k))).filter Nat.Prime, Real.log p / p := by
      rw [show 16 ^ (J + 1) * k = 16 * (16 ^ J * k) by ring]
      simp only [Finset.sum_filter]
      exact (Finset.sum_Ioc_consecutive _ hle (by omega)).symm
    rw [hsplit]
    push_cast
    have := hblock (16 ^ J * k) (le_trans hk hle)
    linarith

/-- Chebyshev's upper bound: $\sum_{k < p \le X} \log p \le X \log 4$. -/
@[category API, AMS 11]
private lemma sum_log_le (k X : ℕ) :
    ∑ p ∈ (Ioc k X).filter Nat.Prime, Real.log p ≤ Real.log 4 * X := by
  calc ∑ p ∈ (Ioc k X).filter Nat.Prime, Real.log p
      ≤ ∑ p ∈ (Ioc 0 X).filter Nat.Prime, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le k)))
          (fun p _ _ => Real.log_natCast_nonneg p)
    _ = Chebyshev.theta X := by rw [Chebyshev.theta, Nat.floor_natCast]
    _ ≤ Real.log 4 * X := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X)

/-! #### Signed admissibility -/

/-- $B$ is admissible: every relation $\sum_{b \in B} \varepsilon_b b = 0$ with
$\varepsilon_b \in \{-1, 0, 1\}$ has $\sum_{b \in B} \varepsilon_b = 0$. -/
private def IsSignedAdmissible (B : Finset ℤ) : Prop :=
  ∀ ε : ℤ → ℤ, (∀ b ∈ B, |ε b| ≤ 1) → ∑ b ∈ B, ε b * b = 0 → ∑ b ∈ B, ε b = 0

/-- The empty set is admissible. -/
@[category API, AMS 5]
private lemma isSignedAdmissible_empty : IsSignedAdmissible ∅ := by
  intro ε _ _
  simp

/-- In an admissible set, equal subset sums have equally many terms. -/
@[category API, AMS 5]
private lemma IsSignedAdmissible.card_eq {B : Finset ℤ} (hB : IsSignedAdmissible B)
    {S T : Finset ℤ} (hT : T ⊆ B) (hS : S ⊆ B) (h : ∑ a ∈ T, a = ∑ b ∈ S, b) : #T = #S := by
  classical
  have key := hB (fun x => (if x ∈ T then 1 else 0) - (if x ∈ S then 1 else 0))
    (fun b _ => by split_ifs <;> simp) (by
      simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT, Finset.inter_eq_right.mpr hS, h,
        sub_self])
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT,
    Finset.inter_eq_right.mpr hS, Finset.sum_const, nsmul_eq_mul, mul_one] at key
  exact_mod_cast sub_eq_zero.mp key

/-! #### Small integer images (Lemma 2 of [Ko26]) -/

/-- Every element of $P$ is a $\{-1, 0, 1\}$-combination of the elements of a maximal admissible
subset $D \subseteq P$. -/
@[category API, AMS 5]
private lemma exists_repr {P D : Finset ℤ} (hDP : D ⊆ P) (hD : IsSignedAdmissible D)
    (hmax : ∀ B ⊆ P, IsSignedAdmissible B → #B ≤ #D) {a : ℤ} (ha : a ∈ P) :
    ∃ η : ℤ → ℤ, (∀ x, |η x| ≤ 1) ∧ ∑ x ∈ D, η x * x = a := by
  classical
  by_cases haD : a ∈ D
  · refine ⟨fun x => if x = a then 1 else 0, fun x => by beta_reduce; split_ifs <;> simp, ?_⟩
    simp [haD]
  -- `insert a D` is not admissible, and a witnessing relation must involve `a`
  have hnot : ¬ IsSignedAdmissible (insert a D) := fun h => by
    have := hmax _ (Finset.insert_subset ha hDP) h
    rw [Finset.card_insert_of_notMem haD] at this
    omega
  simp only [IsSignedAdmissible, not_forall] at hnot
  obtain ⟨ε, hε, hrel, hsum⟩ := hnot
  rw [Finset.sum_insert haD] at hrel hsum
  have hεa : ε a = 1 ∨ ε a = -1 := by
    have h1 := abs_le.mp (hε a (Finset.mem_insert_self a D))
    have h2 : ε a ≠ 0 := fun h0 => by
      rw [h0, zero_mul, zero_add] at hrel
      rw [h0, zero_add] at hsum
      exact hsum (hD ε (fun b hb => hε b (Finset.mem_insert_of_mem hb)) hrel)
    omega
  refine ⟨fun x => if x ∈ D then -ε a * ε x else 0, fun x => ?_, ?_⟩
  · beta_reduce
    split_ifs with hx
    · rw [abs_mul, abs_neg]
      exact mul_le_one₀ (hε a (Finset.mem_insert_self a D)) (abs_nonneg _)
        (hε x (Finset.mem_insert_of_mem hx))
    · simp
  · beta_reduce
    have h : ∑ x ∈ D, ε x * x = -(ε a * a) := by linarith
    calc ∑ x ∈ D, (if x ∈ D then -ε a * ε x else 0) * x = ∑ x ∈ D, -ε a * ε x * x :=
          Finset.sum_congr rfl fun x hx => by rw [if_pos hx]
      _ = -ε a * ∑ x ∈ D, ε x * x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = a := by rw [h]; rcases hεa with h' | h' <;> rw [h'] <;> ring

/-- The representation is injective, so $|P| \le 3^{|D|}$. -/
@[category API, AMS 5]
private lemma card_le_three_pow {P D : Finset ℤ} (η : ℤ → ℤ → ℤ) (hη1 : ∀ a ∈ P, ∀ x, |η a x| ≤ 1)
    (hη2 : ∀ a ∈ P, ∑ x ∈ D, η a x * x = a) : #P ≤ 3 ^ #D := by
  classical
  let F : ℤ → D → ℤ := fun a x => η a x
  have hinj : Set.InjOn F P := by
    intro a ha a' ha' h
    rw [← hη2 a ha, ← hη2 a' ha', ← Finset.sum_coe_sort D, ← Finset.sum_coe_sort D]
    exact Finset.sum_congr rfl fun x _ => by rw [show η a x = η a' x from congrFun h x]
  have hmaps : ∀ a ∈ P, F a ∈ Fintype.piFinset fun _ : D => Finset.Icc (-1 : ℤ) 1 := by
    intro a ha
    rw [Fintype.mem_piFinset]
    exact fun x => Finset.mem_Icc.mpr (abs_le.mp (hη1 a ha x))
  calc #P ≤ #(Fintype.piFinset fun _ : D => Finset.Icc (-1 : ℤ) 1) :=
        Finset.card_le_card_of_injOn F hmaps hinj
    _ = 3 ^ #D := by simp [Fintype.card_piFinset]

/-- A version of Lemma 2 of [Ko26], with the bound $k^{2k+2}$ instead of $k^{2k}$. Let $D$ be a
maximal admissible subset of $P$, where $0 \notin P$, and let $k = |D| + 1$. There are integers
$b_a$ with $|b_a| \le k^{2k+2}$, and $b_a \neq 0$ for at least half of the $a \in P$. Every
relation $\sum_{a \in E} \varepsilon_a a = 0$ with $|E| \le k$ and $\varepsilon_a \in \{-1, 0, 1\}$
implies $\sum_{a \in E} \varepsilon_a b_a = 0$. -/
@[category API, AMS 5]
private lemma exists_small_images {P D : Finset ℤ} (h0 : 0 ∉ P) (hDP : D ⊆ P)
    (hD : IsSignedAdmissible D) (hmax : ∀ B ⊆ P, IsSignedAdmissible B → #B ≤ #D) :
    ∃ b : ℤ → ℤ, #P ≤ 2 * #(P.filter fun a => b a ≠ 0) ∧
      (∀ a ∈ P, |b a| ≤ ((#D + 1 : ℕ) : ℤ) ^ (2 * (#D + 1) + 2)) ∧
      ∀ E ⊆ P, #E ≤ #D + 1 → ∀ ε : ℤ → ℤ, (∀ a ∈ E, |ε a| ≤ 1) →
        ∑ a ∈ E, ε a * a = 0 → ∑ a ∈ E, ε a * b a = 0 := by
  classical
  choose! η hη1 hη2 using fun a (ha : a ∈ P) => exists_repr hDP hD hmax ha
  set k : ℕ := #D + 1 with hk
  -- the rows `w = ∑ ε_a η_a` of signed zero relations with at most `k` terms
  let W : Set (D → ℤ) := {w | ∃ E ⊆ P, #E ≤ k ∧ ∃ ε : ℤ → ℤ, (∀ a ∈ E, |ε a| ≤ 1) ∧
      ∑ a ∈ E, ε a * a = 0 ∧ w = fun i : D => ∑ a ∈ E, ε a * η a i}
  have hWb : ∀ w ∈ W, ∀ i, |w i| ≤ (k : ℤ) := by
    rintro w ⟨E, hE, hEk, ε, hε, -, rfl⟩ i
    calc |∑ a ∈ E, ε a * η a i| ≤ ∑ a ∈ E, |ε a * η a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ E, (1 : ℤ) := Finset.sum_le_sum fun a ha => by
          rw [abs_mul]; exact mul_le_one₀ (hε a ha) (abs_nonneg _) (hη1 a (hE ha) i)
      _ = #E := by simp
      _ ≤ k := by exact_mod_cast hEk
  -- the vector `d` of elements of `D` is orthogonal to every row
  have hWd : ∀ w ∈ W, ∑ i : D, w i * (i : ℤ) = 0 := by
    rintro w ⟨E, hE, -, ε, -, hrel, rfl⟩
    calc ∑ i : D, (∑ a ∈ E, ε a * η a i) * (i : ℤ)
        = ∑ a ∈ E, ε a * ∑ i : D, η a i * (i : ℤ) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ a ∈ E, ε a * a := Finset.sum_congr rfl fun a ha => by
          rw [Finset.sum_coe_sort D (fun x => η a x * x), hη2 a (hE ha)]
      _ = 0 := hrel
  obtain ⟨z, hzW, hzb, hzd⟩ := exists_kernel_vectors W (k : ℤ) (by simp [hk]) hWb
  -- every element of `P` is detected by some `z j`, since `η_a ⬝ d = a ≠ 0`
  have hdet : ∀ a ∈ P, ∃ j, ∑ i : D, η a i * z j i ≠ 0 := by
    intro a ha
    refine hzd (fun i => (i : ℤ)) hWd (fun i => η a i) ?_
    rw [Finset.sum_coe_sort D (fun x => η a x * x), hη2 a ha]
    exact fun h => h0 (h ▸ ha)
  obtain ⟨S, hS⟩ := exists_finset_card_le_two_mul P (fun a j => ∑ i : D, η a i * z j i) hdet
  refine ⟨fun a => ∑ j ∈ S, ∑ i : D, η a i * z j i, hS, fun a ha => ?_, ?_⟩
  · -- size of the images
    have hcard : Fintype.card D = #D := Fintype.card_coe D
    have hZ : ∀ j i, |z j i| ≤ (k.factorial : ℤ) * (k : ℤ) ^ k := fun j i => by
      simpa [hcard, hk] using hzb j i
    have hSk : #S ≤ k := (Finset.card_le_univ S).trans (by rw [hcard]; omega)
    have hfac : (k.factorial : ℤ) ≤ (k : ℤ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    calc |∑ j ∈ S, ∑ i : D, η a i * z j i|
        ≤ ∑ j ∈ S, ∑ i : D, |η a i * z j i| := (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j ∈ S, ∑ _i : D, (k.factorial : ℤ) * (k : ℤ) ^ k := by
          gcongr with j _ i _
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) (hη1 a ha i)).trans (hZ j i)
      _ = #S * (#D * ((k.factorial : ℤ) * (k : ℤ) ^ k)) := by simp
      _ ≤ (k : ℤ) * ((k : ℤ) * ((k : ℤ) ^ k * (k : ℤ) ^ k)) := by
          gcongr
          omega
      _ = ((#D + 1 : ℕ) : ℤ) ^ (2 * (#D + 1) + 2) := by rw [← hk]; ring
  · -- relations with at most `k` terms are preserved
    intro E hE hEk ε hε hrel
    have hw : (fun i : D => ∑ a ∈ E, ε a * η a i) ∈ W := ⟨E, hE, hEk, ε, hε, hrel, rfl⟩
    calc ∑ a ∈ E, ε a * ∑ j ∈ S, ∑ i : D, η a i * z j i
        = ∑ j ∈ S, ∑ i : D, (∑ a ∈ E, ε a * η a i) * z j i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
      _ = 0 := Finset.sum_eq_zero fun j _ => hzW j _ hw

/-! #### Valuations of the images (Section 3 of [Ko26]) -/

/-- Let $p > k$ be prime and $p \nmid u$. At most $k - 1$ elements $a$ satisfy $p^v \mid b_a$ and
$b_a / p^v \equiv u \pmod p$. Otherwise these elements would form an admissible set larger than
$D$. -/
@[category API, AMS 11]
private lemma card_class_le {P D : Finset ℤ} (hmax : ∀ B ⊆ P, IsSignedAdmissible B → #B ≤ #D)
    {b : ℤ → ℤ} (hpres : ∀ E ⊆ P, #E ≤ #D + 1 → ∀ ε : ℤ → ℤ, (∀ a ∈ E, |ε a| ≤ 1) →
        ∑ a ∈ E, ε a * a = 0 → ∑ a ∈ E, ε a * b a = 0)
    {p : ℕ} (hp : p.Prime) (hkp : #D + 1 < p) (v : ℕ) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    #(P.filter fun a => (p : ℤ) ^ v ∣ b a ∧ b a / (p : ℤ) ^ v ≡ u [ZMOD p]) ≤ #D := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (show #D + 1 ≤ _ from hlt)
  have hEP : E ⊆ P := hEsub.trans (Finset.filter_subset _ _)
  have hE : ∀ a ∈ E, ∃ q, b a = (p : ℤ) ^ v * q ∧ q ≡ u [ZMOD p] := fun a ha => by
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp (hEsub ha)).2
    exact ⟨_, (Int.mul_ediv_cancel' h1).symm, h2⟩
  choose! q hq hqu using hE
  have hadm : IsSignedAdmissible E := by
    intro ε hε hrel
    have h1 := hpres E hEP hEcard.le ε hε hrel
    -- divide the image relation by `p^v`
    have h2 : ∑ a ∈ E, ε a * q a = 0 := by
      have : (p : ℤ) ^ v * ∑ a ∈ E, ε a * q a = 0 := by
        rw [Finset.mul_sum, ← h1]
        exact Finset.sum_congr rfl fun a ha => by rw [hq a ha]; ring
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    -- reduce modulo `p`
    have := Fact.mk hp
    have h3 : ((∑ a ∈ E, ε a : ℤ) : ZMod p) * (u : ZMod p) = 0 := by
      have h4 : ((∑ a ∈ E, ε a * q a : ℤ) : ZMod p) = 0 := by rw [h2]; simp
      push_cast at h4 ⊢
      rw [Finset.sum_mul, ← h4]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr (hqu a ha)]
    have hu' : (u : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h5 := (mul_eq_zero.mp h3).resolve_right hu'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h5
    refine Int.eq_zero_of_abs_lt_dvd h5 ?_
    calc |∑ a ∈ E, ε a| ≤ ∑ a ∈ E, |ε a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ E, (1 : ℤ) := Finset.sum_le_sum hε
      _ = #E := by simp
      _ < p := by rw [hEcard]; exact_mod_cast hkp
  have := hmax E hEP hadm
  omega

/-- Each valuation level $\{a \in A_0 : v_p(b_a) = v\}$ has at most $d(p - 1)$ elements. -/
@[category API, AMS 11]
private lemma card_level_le {A0 : Finset ℤ} {b : ℤ → ℤ} (hb : ∀ a ∈ A0, b a ≠ 0) {p : ℕ}
    (hp : p.Prime) {d : ℕ} (hclass : ∀ v : ℕ, ∀ u : ℤ, ¬ (p : ℤ) ∣ u →
      #(A0.filter fun a => (p : ℤ) ^ v ∣ b a ∧ b a / (p : ℤ) ^ v ≡ u [ZMOD p]) ≤ d)
    (v : ℕ) : #(A0.filter fun a => (b a).natAbs.factorization p = v) ≤ d * (p - 1) := by
  classical
  set L := A0.filter fun a => (b a).natAbs.factorization p = v
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- `p^v ∣ b a` and `p ∤ b a / p^v`
  have hsplit : ∀ a ∈ L, (p : ℤ) ^ v ∣ b a ∧ ¬ (p : ℤ) ∣ b a / (p : ℤ) ^ v := by
    intro a ha
    obtain ⟨haA, hv⟩ := Finset.mem_filter.mp ha
    have hne : (b a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hb a haA)
    have hdvd : (p : ℤ) ^ v ∣ b a := by
      rw [← hv]; exact_mod_cast Int.natCast_dvd.mpr (Nat.ordProj_dvd _ _)
    refine ⟨hdvd, fun h => ?_⟩
    apply Nat.pow_succ_factorization_not_dvd hne hp
    rw [hv, ← Int.natCast_dvd, Nat.cast_pow, pow_succ]
    conv_rhs => rw [← Int.mul_ediv_cancel' hdvd]
    exact mul_dvd_mul_left _ h
  let r : ℤ → ℤ := fun a => b a / (p : ℤ) ^ v % p
  have hr : ∀ a ∈ L, r a ∈ Finset.Ioo (0 : ℤ) p := by
    intro a ha
    refine Finset.mem_Ioo.mpr ⟨lt_of_le_of_ne (Int.emod_nonneg _ hp0.ne') fun h => ?_,
      Int.emod_lt_of_pos _ hp0⟩
    exact (hsplit a ha).2 (Int.dvd_of_emod_eq_zero h.symm)
  have hfib : ∀ u ∈ L.image r, #(L.filter fun a => r a = u) ≤ d := by
    intro u hu
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hu
    have hu0 : ¬ (p : ℤ) ∣ r a₀ := fun h => by
      have := Finset.mem_Ioo.mp (hr a₀ ha₀)
      exact absurd (Int.le_of_dvd this.1 h) (not_le.mpr this.2)
    refine le_trans (Finset.card_le_card fun a ha => ?_) (hclass v (r a₀) hu0)
    obtain ⟨haL, hra⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haL).1, (hsplit a haL).1, ?_⟩
    change b a / (p : ℤ) ^ v % p = r a₀ % p
    rw [← hra]
    exact (Int.emod_emod _ _).symm
  calc #L ≤ d * #(L.image r) := Finset.card_le_mul_card_image L d hfib
    _ ≤ d * (p - 1) := by
      gcongr
      calc #(L.image r) ≤ #(Finset.Ioo (0 : ℤ) p) := Finset.card_le_card fun u hu => by
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
            exact hr a ha
        _ = p - 1 := by simp

/-- If each valuation level has at most $L$ elements, then
$\sum_{a \in A_0} v_p(b_a) \ge J(|A_0| - JL)$. -/
@[category API, AMS 11]
private lemma sum_factorization_ge {A0 : Finset ℤ} {b : ℤ → ℤ} {p L : ℕ}
    (hlevel : ∀ v : ℕ, #(A0.filter fun a => (b a).natAbs.factorization p = v) ≤ L) (J : ℕ) :
    (J : ℝ) * (#A0 - J * L) ≤ ∑ a ∈ A0, ((b a).natAbs.factorization p : ℝ) := by
  classical
  set f : ℤ → ℕ := fun a => (b a).natAbs.factorization p
  have hlow : #(A0.filter fun a => f a < J) ≤ J * L := by
    calc #(A0.filter fun a => f a < J)
        = ∑ v ∈ range J, #((A0.filter fun a => f a < J).filter fun a => f a = v) :=
          Finset.card_eq_sum_card_fiberwise fun a ha => by
            simpa using (Finset.mem_filter.mp ha).2
      _ ≤ ∑ v ∈ range J, #(A0.filter fun a => f a = v) :=
          Finset.sum_le_sum fun v _ => Finset.card_le_card
            (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      _ ≤ ∑ _v ∈ range J, L := Finset.sum_le_sum fun v _ => hlevel v
      _ = J * L := by simp
  have hsplit := Finset.card_filter_add_card_filter_not (s := A0) (fun a => J ≤ f a)
  simp only [not_le] at hsplit
  have hhigh : (J : ℝ) * #(A0.filter fun a => J ≤ f a) ≤ ∑ a ∈ A0, (f a : ℝ) := by
    calc (J : ℝ) * #(A0.filter fun a => J ≤ f a)
        = ∑ _a ∈ A0.filter (fun a => J ≤ f a), (J : ℝ) := by simp [mul_comm]
      _ ≤ ∑ a ∈ A0.filter (fun a => J ≤ f a), (f a : ℝ) :=
          Finset.sum_le_sum fun a ha => by exact_mod_cast (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a ∈ A0, (f a : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun _ _ _ => by positivity
  have h1 : (#A0 : ℝ) - J * L ≤ #(A0.filter fun a => J ≤ f a) := by
    have e : (#A0 : ℝ) = #(A0.filter fun a => J ≤ f a) + #(A0.filter fun a => f a < J) := by
      exact_mod_cast hsplit.symm
    have h2 : (#(A0.filter fun a => f a < J) : ℝ) ≤ J * L := by exact_mod_cast hlow
    linarith
  calc (J : ℝ) * (#A0 - J * L) ≤ J * #(A0.filter fun a => J ≤ f a) := by gcongr
    _ ≤ _ := hhigh

/-- Korsky's bound $\sum_{a \in A_0} v_p(b_a) \ge m^2/(2kp) - m$ for $m = |A_0|$, in the weaker
form $m^2/(4kp) - m/2$. -/
@[category API, AMS 11]
private lemma sum_factorization_ge' {A0 : Finset ℤ} {b : ℤ → ℤ} {p d k : ℕ} (hdk : d ≤ k)
    (hk : 0 < k) (hp : 0 < p)
    (hlevel : ∀ v : ℕ, #(A0.filter fun a => (b a).natAbs.factorization p = v) ≤ d * (p - 1)) :
    (#A0 : ℝ) ^ 2 / (4 * k * p) - #A0 / 2 ≤
      ∑ a ∈ A0, ((b a).natAbs.factorization p : ℝ) := by
  set m : ℝ := (#A0 : ℝ)
  set J : ℕ := ⌊m / (2 * k * p)⌋₊
  have hJ := sum_factorization_ge hlevel J
  have hkp : (0 : ℝ) < k * p := by positivity
  have hm : 0 ≤ m := by positivity
  have hJle : (J : ℝ) ≤ m / (2 * k * p) := Nat.floor_le (by positivity)
  have hJgt : m / (2 * k * p) - 1 < J := by
    have := Nat.lt_floor_add_one (m / (2 * k * p)); linarith
  have hdp : (((d * (p - 1) : ℕ)) : ℝ) ≤ k * p := by
    exact_mod_cast Nat.mul_le_mul hdk (Nat.sub_le _ _)
  have h1 : (J : ℝ) * ((d * (p - 1) : ℕ) : ℝ) ≤ m / 2 := by
    calc (J : ℝ) * ((d * (p - 1) : ℕ) : ℝ) ≤ m / (2 * k * p) * (k * p) := by gcongr
      _ = m / 2 := by field_simp
  calc m ^ 2 / (4 * k * p) - m / 2 = (m / (2 * k * p) - 1) * (m / 2) := by
        field_simp; ring
    _ ≤ J * (m / 2) := by gcongr
    _ ≤ J * (m - J * ((d * (p - 1) : ℕ) : ℝ)) := by gcongr; linarith
    _ ≤ _ := hJ

/-- Prime factorization: $\sum_{p \in Q} v_p(n) \log p \le \log n$ for every finite set $Q$. -/
@[category API, AMS 11]
private lemma sum_factorization_mul_log_le (n : ℕ) (Pr : Finset ℕ) :
    ∑ p ∈ Pr, (n.factorization p : ℝ) * Real.log p ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization n, Finsupp.sum]
  calc ∑ p ∈ Pr, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ Pr.filter (· ∈ n.factorization.support), (n.factorization p : ℝ) * Real.log p := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with h
        · rfl
        · simp [Finsupp.notMem_support_iff.mp h]
    _ ≤ ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
          fun p _ _ => mul_nonneg (by positivity) (Real.log_natCast_nonneg p)

/-! #### The main inequality -/

/-- The main inequality of [Ko26]. Assume $\sum_{k < p \le 16^J k} \log p / p \ge J \log 2 / 4$
for all $k \ge y_0$ and all $J$. Then some admissible $B \subseteq A$ has $|A| \le 3^{|B|} + 1$,
and if $k = |B| + 1 \ge y_0$ then
$\frac{|A| - 1}{2} \cdot \frac{J \log 2}{4} \le 4k((2k+2)\log k + 16^J k \log 2)$ for all $J$. -/
@[category API, AMS 5 11]
private lemma korsky_ineq {y₀ : ℕ} (hy₀ : ∀ k : ℕ, y₀ ≤ k → ∀ J : ℕ,
      (J : ℝ) * (Real.log 2 / 4) ≤
        ∑ p ∈ (Ioc k (16 ^ J * k)).filter Nat.Prime, Real.log p / p)
    (A : Finset ℤ) : ∃ B ⊆ A, IsSignedAdmissible B ∧ #A ≤ 3 ^ #B + 1 ∧
      ∀ J : ℕ, y₀ ≤ #B + 1 →
        ((#A : ℝ) - 1) / 2 * (J * (Real.log 2 / 4)) ≤
          4 * (#B + 1) * ((2 * (#B + 1) + 2) * Real.log (#B + 1) +
            16 ^ J * (#B + 1) * Real.log 2) := by
  classical
  have hAP : #A ≤ #(A.erase 0) + 1 := by
    have := Finset.pred_card_le_card_erase (s := A) (a := 0); omega
  set P := A.erase 0 with hP
  have h0 : (0 : ℤ) ∉ P := Finset.notMem_erase 0 A
  -- a maximal admissible subset `D` of `P`
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image (P.powerset.filter IsSignedAdmissible)
    Finset.card ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, isSignedAdmissible_empty⟩⟩
  obtain ⟨hDP, hD⟩ := Finset.mem_filter.mp hDmem
  rw [Finset.mem_powerset] at hDP
  have hmax : ∀ B ⊆ P, IsSignedAdmissible B → #B ≤ #D := fun B hB hBa =>
    hDmax B (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB, hBa⟩)
  refine ⟨D, hDP.trans (Finset.erase_subset 0 A), hD, ?_, fun J hk => ?_⟩
  · choose! η hη1 hη2 using fun a (ha : a ∈ P) => exists_repr hDP hD hmax ha
    have := card_le_three_pow η hη1 hη2
    omega
  obtain ⟨b, hbP, hbM, hpres⟩ := exists_small_images h0 hDP hD hmax
  set k : ℕ := #D + 1 with hk_def
  set A0 := P.filter fun a => b a ≠ 0
  set m : ℕ := #A0
  have hb0 : ∀ a ∈ A0, b a ≠ 0 := fun a ha => (Finset.mem_filter.mp ha).2
  set Pr := (Ioc k (16 ^ J * k)).filter Nat.Prime
  -- for every prime `p > k`: `∑_a v_p(b_a) ≥ m²/(4kp) - m/2`
  have hval : ∀ p ∈ Pr,
      (m : ℝ) ^ 2 / (4 * k * p) - m / 2 ≤ ∑ a ∈ A0, ((b a).natAbs.factorization p : ℝ) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    have hkp : k < p := (Finset.mem_Ioc.mp hpI).1
    refine sum_factorization_ge' (d := #D) (by omega) (by omega) hpp.pos fun v => ?_
    refine card_level_le hb0 hpp (fun v u hu => ?_) v
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
      (card_class_le hmax hpres hpp hkp v hu)
  set S1 := ∑ p ∈ Pr, Real.log p / p
  set S0 := ∑ p ∈ Pr, Real.log p
  -- lower bound for `∑_a log |b_a|` from the valuations
  have hlow : (m : ℝ) ^ 2 / (4 * k) * S1 - m / 2 * S0 ≤ ∑ a ∈ A0, Real.log (b a).natAbs := by
    calc (m : ℝ) ^ 2 / (4 * k) * S1 - m / 2 * S0
        = ∑ p ∈ Pr, ((m : ℝ) ^ 2 / (4 * k * p) - m / 2) * Real.log p := by
          simp only [S1, S0, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have : (p : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
          field_simp
      _ ≤ ∑ p ∈ Pr, (∑ a ∈ A0, ((b a).natAbs.factorization p : ℝ)) * Real.log p :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_right (hval p hp) (Real.log_natCast_nonneg p)
      _ = ∑ a ∈ A0, ∑ p ∈ Pr, ((b a).natAbs.factorization p : ℝ) * Real.log p := by
          simp only [Finset.sum_mul]; exact Finset.sum_comm
      _ ≤ ∑ a ∈ A0, Real.log (b a).natAbs :=
          Finset.sum_le_sum fun a _ => sum_factorization_mul_log_le _ Pr
  -- upper bound from `|b_a| ≤ k^(2k+2)`
  have hup : ∑ a ∈ A0, Real.log (b a).natAbs ≤ m * ((2 * k + 2) * Real.log k) := by
    calc ∑ a ∈ A0, Real.log (b a).natAbs ≤ ∑ _a ∈ A0, (2 * k + 2) * Real.log k := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hpos : (0 : ℝ) < (b a).natAbs := by exact_mod_cast Int.natAbs_pos.mpr (hb0 a ha)
          have hba : ((b a).natAbs : ℤ) ≤ (k : ℤ) ^ (2 * k + 2) := by
            rw [Int.natCast_natAbs]; exact hbM a (Finset.mem_filter.mp ha).1
          calc Real.log (b a).natAbs ≤ Real.log ((k : ℝ) ^ (2 * k + 2)) :=
                Real.log_le_log hpos (by exact_mod_cast hba)
            _ = (2 * k + 2) * Real.log k := by rw [Real.log_pow]; push_cast; ring
      _ = m * ((2 * k + 2) * Real.log k) := by simp [m]
  have hkpos : (0 : ℝ) < k := by positivity
  have hS0nn : 0 ≤ S0 := Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun p _ =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  -- `m S1 ≤ 4k ((2k+2) log k + S0/2)`
  have hmain : (m : ℝ) * S1 ≤ 4 * k * ((2 * k + 2) * Real.log k + S0 / 2) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0, Nat.cast_zero, zero_mul]; positivity
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    by_contra hcon
    push Not at hcon
    have h := mul_lt_mul_of_pos_left hcon (div_pos hmR (by positivity : (0 : ℝ) < 4 * k))
    have e1 : (m : ℝ) / (4 * k) * (4 * k * ((2 * k + 2) * Real.log k + S0 / 2)) =
        m * ((2 * k + 2) * Real.log k) + m / 2 * S0 := by field_simp
    have e2 : (m : ℝ) / (4 * k) * (m * S1) = m ^ 2 / (4 * k) * S1 := by ring
    rw [e1, e2] at h
    linarith [hlow.trans hup]
  have hS1 : (J : ℝ) * (Real.log 2 / 4) ≤ S1 := hy₀ k hk J
  have hS0 : S0 ≤ Real.log 4 * ((16 ^ J * k : ℕ) : ℝ) := sum_log_le k (16 ^ J * k)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hAm : ((#A : ℝ) - 1) / 2 ≤ m := by
    have h1 : (#A : ℝ) ≤ #P + 1 := by exact_mod_cast hAP
    have h2 : (#P : ℝ) ≤ 2 * m := by exact_mod_cast hbP
    linarith
  have hkR : (k : ℝ) = #D + 1 := by simp [hk_def]
  calc ((#A : ℝ) - 1) / 2 * (J * (Real.log 2 / 4)) ≤ m * S1 :=
        (mul_le_mul_of_nonneg_right hAm (by positivity)).trans
          (mul_le_mul_of_nonneg_left hS1 (by positivity))
    _ ≤ 4 * k * ((2 * k + 2) * Real.log k + S0 / 2) := hmain
    _ ≤ 4 * k * ((2 * k + 2) * Real.log k + 16 ^ J * k * Real.log 2) := by
        gcongr
        rw [hlog4] at hS0
        push_cast at hS0
        linarith
    _ = _ := by rw [hkR]

/-! #### Korsky's bound -/

/-- Korsky's bound [Ko26]: for large $n$, every set of $n$ integers has an admissible subset of
size at least $c\sqrt{n\log\log n/\log n}$. -/
@[category API, AMS 5 11]
private lemma korsky : ∃ c > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ A : Finset ℤ, #A = n →
    ∃ B ⊆ A, IsSignedAdmissible B ∧ c * √(n * Real.log (Real.log n) / Real.log n) ≤ #B := by
  obtain ⟨y₀, hy₀⟩ := exists_sum_log_div_ge
  refine ⟨1 / 200, by norm_num, 3 ^ y₀ + ⌈Real.exp 256⌉₊ + 2, fun n hn A hA => ?_⟩
  obtain ⟨B, hBA, hB, hcard, hineq⟩ := korsky_ineq hy₀ A
  refine ⟨B, hBA, hB, ?_⟩
  -- `B` is large, since `n ≤ 3^|B| + 1`
  have hBy : y₀ < #B := by
    by_contra h
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (not_lt.mp h)
    omega
  have hBn : #B ≤ n := hA ▸ Finset.card_le_card hBA
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.le_add_left 2 _).trans hn
  have hnexp : Real.exp 256 ≤ n := (Nat.le_ceil _).trans (by
    exact_mod_cast (Nat.le_add_left _ _).trans ((Nat.le_add_right _ 2).trans hn))
  set L := Real.log n with hL
  have hL256 : 256 ≤ L := by rw [hL, Real.le_log_iff_exp_le (by linarith)]; exact hnexp
  have hLpos : 0 < L := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlogL : 8 * Real.log 2 ≤ Real.log L := by
    calc 8 * Real.log 2 = Real.log 256 := by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      _ ≤ Real.log L := Real.log_le_log (by norm_num) hL256
  -- the number `J` of blocks
  set t := Real.log L / Real.log 16 with ht
  set J : ℕ := ⌊t⌋₊ with hJ
  have ht2 : 2 ≤ t := by rw [ht, le_div_iff₀ (by positivity)]; linarith
  have hJt : (J : ℝ) ≤ t := by rw [hJ]; exact Nat.floor_le (by linarith)
  have hJt' : t / 2 ≤ J := by
    have := Nat.lt_floor_add_one t
    rw [← hJ] at this
    linarith
  have h16J : (16 : ℝ) ^ J ≤ L := by
    rw [← Real.log_le_log_iff (by positivity : (0 : ℝ) < 16 ^ J) hLpos, Real.log_pow]
    rwa [ht, le_div_iff₀ (by positivity)] at hJt
  have hJlog : Real.log L / 32 ≤ J * (Real.log 2 / 4) := by
    rw [ht, hlog16, div_div, div_le_iff₀ (by positivity)] at hJt'
    linarith
  -- bounds in terms of `|B|`
  have hβ1 : (1 : ℝ) ≤ #B := by exact_mod_cast (show 1 ≤ #B by omega)
  have hβn : (#B : ℝ) ≤ n := by exact_mod_cast hBn
  have hlogK0 : 0 ≤ Real.log ((#B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogK : Real.log ((#B : ℝ) + 1) ≤ 2 * L := by
    calc Real.log ((#B : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * L := by rw [Real.log_pow, hL]; norm_num
  have hineq' := hineq J (by omega)
  rw [hA] at hineq'
  have hR : 4 * ((#B : ℝ) + 1) * ((2 * ((#B : ℝ) + 1) + 2) * Real.log ((#B : ℝ) + 1) +
      16 ^ J * ((#B : ℝ) + 1) * Real.log 2) ≤ 36 * ((#B : ℝ) + 1) ^ 2 * L := by
    have e1 : (2 * ((#B : ℝ) + 1) + 2) * Real.log ((#B : ℝ) + 1) ≤
        (4 * ((#B : ℝ) + 1)) * (2 * L) :=
      mul_le_mul (by linarith) hlogK hlogK0 (by positivity)
    have e2 : (16 : ℝ) ^ J * ((#B : ℝ) + 1) * Real.log 2 ≤ L * ((#B : ℝ) + 1) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right h16J (by positivity)) (by linarith)
        (by linarith) (by positivity)
    calc _ ≤ 4 * ((#B : ℝ) + 1) * ((4 * ((#B : ℝ) + 1)) * (2 * L) + L * ((#B : ℝ) + 1) * 1) :=
          mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity)
      _ = 36 * ((#B : ℝ) + 1) ^ 2 * L := by ring
  have hLow : (n : ℝ) * Real.log L / 128 ≤ ((n : ℝ) - 1) / 2 * (J * (Real.log 2 / 4)) := by
    calc (n : ℝ) * Real.log L / 128 = (n / 4) * (Real.log L / 32) := by ring
      _ ≤ _ := mul_le_mul (by linarith) hJlog (by linarith) (by linarith)
  have hβsq : ((#B : ℝ) + 1) ^ 2 ≤ 4 * (#B : ℝ) ^ 2 := by nlinarith
  have hX : (n : ℝ) * Real.log L / L ≤ 40000 * (#B : ℝ) ^ 2 := by
    rw [div_le_iff₀ hLpos]
    have h1 := hLow.trans (hineq'.trans hR)
    have h2 : 36 * ((#B : ℝ) + 1) ^ 2 * L ≤ 36 * (4 * (#B : ℝ) ^ 2) * L := by gcongr
    linarith [mul_nonneg (sq_nonneg (#B : ℝ)) hLpos.le]
  have hsq : √((n : ℝ) * Real.log L / L) ≤ 200 * #B :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  linarith

end Korsky

/-- Korsky [Ko26] proved that $h(n) \gg \sqrt{n\log\log n/\log n}$. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.sqrt_loglog_div_log_isBigO :
    (fun n : ℕ ↦ √(n * Real.log (Real.log n) / Real.log n)) =O[atTop]
      fun n ↦ (subsetSumThreshold n : ℝ) := by
  obtain ⟨c, hc, N₀, hN₀⟩ := korsky
  refine Asymptotics.IsBigO.of_bound (1 / c) ?_
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hsep : IsSubsetSumSeparatingCard n ⌈c * √(n * Real.log (Real.log n) / Real.log n)⌉₊ := by
    intro A hA
    obtain ⟨B, hBA, hB, hcB⟩ := hN₀ n hn A hA
    exact ⟨B, hBA, Nat.ceil_le.mpr hcB, fun T hT S hS _ _ h => hB.card_eq hT hS h⟩
  have hbdd : BddAbove {m | IsSubsetSumSeparatingCard n m} := by
    refine ⟨n, fun m hm => ?_⟩
    obtain ⟨B, hBA, hmB, -⟩ := hm ((Finset.range n).image (fun i : ℕ => (i : ℤ)))
      (by rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range])
    calc m ≤ #B := hmB
      _ ≤ #((Finset.range n).image (fun i : ℕ => (i : ℤ))) := Finset.card_le_card hBA
      _ ≤ n := Finset.card_image_le.trans (Finset.card_range n).le
  have key : c * √(n * Real.log (Real.log n) / Real.log n) ≤ subsetSumThreshold n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_csSup hbdd hsep)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith

/-- $(n\log(n))^{1/3} = o(\sqrt{n\log\log n/\log n})$. -/
@[category API, AMS 5]
private lemma cube_root_linearithmic_isLittleO :
    (fun n : ℕ ↦ (n * Real.log n) ^ ((1 : ℝ) / 3)) =o[atTop]
      fun n : ℕ ↦ √(n * Real.log (Real.log n) / Real.log n) := by
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := 5)).comp_tendsto
    tendsto_natCast_atTop_atTop
  refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
  filter_upwards [hlog.bound (pow_pos hc 6),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp (Real.exp 1))] with n h2 hx
  simp only [Function.comp_apply, id] at h2
  have hxpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL1 : Real.exp 1 ≤ Real.log n := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hLpos : 0 < Real.log n := lt_of_lt_of_le (Real.exp_pos _) hL1
  have hLL : 1 ≤ Real.log (Real.log n) := (Real.le_log_iff_exp_le hLpos).mpr hL1
  set a := √(n * Real.log (Real.log n) / Real.log n) with ha
  set b := ((n : ℝ) * Real.log n) ^ ((1 : ℝ) / 3) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg ha0, Real.norm_of_nonneg hb0]
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log n ^ 5 by positivity),
    Real.norm_of_nonneg hxpos.le] at h2
  have ha2 : a ^ 2 = n * Real.log (Real.log n) / Real.log n :=
    Real.sq_sqrt (div_nonneg (mul_nonneg hxpos.le (by linarith)) hLpos.le)
  have hb3 : b ^ 3 = n * Real.log n := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  refine (pow_le_pow_iff_left₀ hb0 (by positivity) (show 6 ≠ 0 by norm_num)).mp ?_
  calc b ^ 6 = ((n : ℝ) * Real.log n) ^ 2 := by rw [← hb3]; ring
    _ ≤ c ^ 6 * ((n : ℝ) / Real.log n) ^ 3 := by
        rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hLpos 3)]
        have e : ((n : ℝ) * Real.log n) ^ 2 * Real.log n ^ 3 =
            (n : ℝ) ^ 2 * Real.log n ^ 5 := by ring
        rw [e, show c ^ 6 * (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * (c ^ 6 * n) by ring]
        gcongr
    _ ≤ c ^ 6 * (a ^ 2) ^ 3 := by
        rw [ha2]
        gcongr
        exact le_mul_of_one_le_right hxpos.le hLL
    _ = (c * a) ^ 6 := by ring

/-- Erdős [Er62c] and Choi [Ch74b] proved that $(n\log(n))^{1/3}\ll h(n)$. This also follows from
`erdos_789.variants.sqrt_loglog_div_log_isBigO`. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.cube_root_linearithmic_isBigO :
    (fun n : ℕ ↦ (n * Real.log n) ^ ((1 : ℝ) / 3)) =O[atTop]
      fun n ↦ (subsetSumThreshold n : ℝ) :=
  cube_root_linearithmic_isLittleO.isBigO.trans erdos_789.variants.sqrt_loglog_div_log_isBigO

/-- It is not true that $h(n) = O((n\log(n))^{1/3})$. This follows from
`erdos_789.variants.sqrt_loglog_div_log_isBigO` [Ko26]. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.isBigO_cube_root_linearithmic :
    ¬ (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) := by
  intro h
  refine Asymptotics.isLittleO_irrefl' ?_ (cube_root_linearithmic_isLittleO.trans_isBigO
    (erdos_789.variants.sqrt_loglog_div_log_isBigO.trans h))
  refine (Filter.eventually_atTop.2 ⟨2, fun n hn => ?_⟩).frequently
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact norm_ne_zero_iff.mpr (Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.log_pos hn')) _).ne'

/-- It is not true that $h(n) = \Theta((n\log(n))^{1/3})$. This follows from
`erdos_789.variants.isBigO_cube_root_linearithmic`. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.cube_root_linearithmic :
    ¬ (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) :=
  fun h ↦ erdos_789.variants.isBigO_cube_root_linearithmic h.isBigO

end Erdos789

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
# Erdős Problem 176

*Reference:* [erdosproblems.com/176](https://www.erdosproblems.com/176)

Let $N(k, \ell)$ be the least $N$ such that every $f : \{1, \dots, N\} \to \{-1, 1\}$ admits a
$k$-term arithmetic progression $P \subseteq \{1, \dots, N\}$ with
$\left|\sum_{n \in P} f(n)\right| \ge \ell$. Find good upper bounds for $N(k, \ell)$.
Is it true that for every $c > 0$ there is $C > 1$ with $N(k, ck) \le C^k$?
What about $N(k, 2) \le C^k$ or $N(k, \sqrt{k}) \le C^k$?

This file states the three questions. It also proves the $N(k, 2)$ question, and the
$N(k, c\sqrt{k})$ question for every fixed $0 \le c < 1$, with the polynomial bounds
$N(k, 2) \le 50 k^3$ and $N(k, c\sqrt{k}) \le 4 \lceil 2/(1-c^2) \rceil^2 k^3$.

The proof is a second-moment argument. Fix $D$. Sum the squared signed sums of all $k$-term
progressions with common difference $e - e'$, over $0 \le e, e' < D$. A change of variables
rewrites this total as a sum of squares. Its diagonal part is at least $k D^2 N$. If every
progression inside $\{1, \dots, N\}$ has squared sum at most $L < k$, the total is at most
$D^2 (N L + 4 k^2 (k - 1) D) + D k^2 N$. This is a contradiction when $N$ is large.
-/

@[expose] public section

open scoped BigOperators

namespace Erdos176

/-- `APProp k ℓ N`: every `±1`-colouring `f` of `{1, …, N}` admits a `k`-term arithmetic
progression `a, a + d, …, a + (k-1) d` (with `d ≥ 1`) inside `{1, …, N}` whose signed sum
has absolute value at least `ℓ`. -/
def APProp (k : ℕ) (ℓ : ℝ) (N : ℕ) : Prop :=
  ∀ f : ℕ → ℤ, (∀ n, 1 ≤ n → n ≤ N → f n = 1 ∨ f n = -1) →
    ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
      ℓ ≤ |((∑ i ∈ Finset.range k, f (a + i * d) : ℤ) : ℝ)|

/-- `N(k, ℓ)`: the least `N` with `APProp k ℓ N` (by convention `0` if no such `N` exists). -/
noncomputable def erdosN (k : ℕ) (ℓ : ℝ) : ℕ := sInf {N | APProp k ℓ N}

/-! ### The open questions -/

/-- Is it true that for every $c > 0$ there is $C > 1$ with $N(k, ck) \le C^k$ for all $k$?

For $c > 1$ no $N$ exists, so `erdosN` is `0` and the bound holds trivially. -/
@[category research open, AMS 5 11]
theorem erdos_176 : answer(sorry) ↔
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k → (erdosN k (c * k) : ℝ) ≤ C ^ k := by
  sorry

/-- Is there $C > 1$ with $N(k, \sqrt{k}) \le C^k$ for all $k \ge 1$? -/
@[category research open, AMS 5 11]
theorem erdos_176.variants.sqrt : answer(sorry) ↔
    ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k → (erdosN k (√(k:ℝ)) : ℝ) ≤ C ^ k := by
  sorry

/-! ### The second-moment argument -/

/-- Shifting the summation variable does not change a sum over a large enough window. -/
@[category API, AMS 5 11]
lemma sum_shift (F : ℤ → ℤ) (lo hi M c : ℤ) (hF : ∀ x, x < lo ∨ hi < x → F x = 0)
    (h1 : -M ≤ lo) (h2 : hi ≤ M) (h3 : -M ≤ lo - c) (h4 : hi - c ≤ M) :
    ∑ a ∈ Finset.Icc (-M) M, F (a + c) = ∑ a ∈ Finset.Icc (-M) M, F a := by
  have key : ∀ s : Finset ℤ, Finset.Icc lo hi ⊆ s →
      ∑ a ∈ s, F a = ∑ a ∈ Finset.Icc lo hi, F a := by
    intro s hs
    symm
    apply Finset.sum_subset hs
    intro x _ hx
    apply hF
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    exact hx
  have e : ∑ a ∈ Finset.Icc (-M) M, F (a + c) = ∑ x ∈ Finset.Icc (-M + c) (M + c), F x := by
    rw [← Finset.map_add_right_Icc, Finset.sum_map]
    rfl
  rw [e, key _ ?_, key (Finset.Icc (-M) M) ?_]
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega

/-- Reversing a progression turns common difference `d` into `-d`. -/
@[category API, AMS 5 11]
lemma S_reflect (k : ℕ) (g : ℤ → ℤ) (a d : ℤ) :
    ∑ i ∈ Finset.range k, g (a + i * d) =
      ∑ i ∈ Finset.range k, g (a + ((k:ℤ) - 1) * d + i * (-d)) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < k := Finset.mem_range.1 hi
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

section Core

variable (k D N L : ℕ) (g : ℤ → ℤ)
  (hsupp : ∀ x, (x < 1 ∨ (N:ℤ) < x) → g x = 0)
  (hval : ∀ x : ℤ, 1 ≤ x → x ≤ N → g x ^ 2 = 1)

include hsupp hval

/-- A colouring extended by zero takes values of absolute value at most `1`. -/
@[category API, AMS 5 11]
lemma abs_g_le (x : ℤ) : |g x| ≤ 1 := by
  by_cases h : 1 ≤ x ∧ x ≤ N
  · have := hval x h.1 h.2
    have h0 : |g x| ^ 2 = 1 := by rw [sq_abs]; exact this
    nlinarith [abs_nonneg (g x)]
  · rw [hsupp x (by omega)]; simp

/-- The sum of `g ^ 2` over a window containing `{1, …, N}` is `N`. -/
@[category API, AMS 5 11]
lemma sum_sq_g (M : ℤ) (hM : (N:ℤ) ≤ M) :
    ∑ a ∈ Finset.Icc (-M) M, g a ^ 2 = N := by
  rw [← Finset.sum_subset (s₁ := Finset.Icc (1:ℤ) N)]
  · rw [Finset.sum_congr rfl
      (fun x hx => hval x (Finset.mem_Icc.1 hx).1 (Finset.mem_Icc.1 hx).2)]
    simp
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x _ hx
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    rw [hsupp x (by omega)]; simp

/-- The trivial bound: a `k`-term signed sum has square at most `k ^ 2`. -/
@[category API, AMS 5 11]
lemma S_sq_le (a d : ℤ) : (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ (k:ℤ) ^ 2 := by
  have h : |∑ i ∈ Finset.range k, g (a + i * d)| ≤ k := by
    calc _ ≤ ∑ i ∈ Finset.range k, |g (a + i * d)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range k, (1:ℤ) :=
          Finset.sum_le_sum (fun i _ => abs_g_le N g hsupp hval _)
      _ = k := by simp
  have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  simpa using this

/-- Pointwise bound on a squared progression sum: `L` when the progression lies inside
`{1, …, N}`, `k ^ 2` near the boundary, and `0` far outside. -/
@[category API, AMS 5 11]
lemma S_sq_pointwise (hk : 1 ≤ k)
    (hap : ∀ a d : ℤ, 0 < d → 1 ≤ a → a + ((k:ℤ) - 1) * d ≤ N →
      (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ L)
    (a d : ℤ) (hd : d ≠ 0) :
    (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤
      (if a ∈ Finset.Icc (1:ℤ) N then (L:ℤ) else 0) +
      (if a ∈ Finset.Icc (1 - ((k:ℤ) - 1) * |d|) (((k:ℤ) - 1) * |d|) ∪
          Finset.Icc ((N:ℤ) + 1 - ((k:ℤ) - 1) * |d|) (N + ((k:ℤ) - 1) * |d|)
        then (k:ℤ) ^ 2 else 0) := by
  have hbd : ∀ i < k, |(i:ℤ) * d| ≤ ((k:ℤ) - 1) * |d| := by
    intro i hi
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ i)]
    have : (i:ℤ) ≤ (k:ℤ) - 1 := by omega
    exact mul_le_mul_of_nonneg_right this (abs_nonneg d)
  have hLnn : (0:ℤ) ≤ L := by positivity
  have hk2 : (0:ℤ) ≤ (k:ℤ) ^ 2 := by positivity
  by_cases hall : ∀ i < k, 1 ≤ a + i * d ∧ a + i * d ≤ N
  · have ha0 := hall 0 hk
    simp only [Nat.cast_zero, zero_mul, add_zero] at ha0
    have ha : a ∈ Finset.Icc (1:ℤ) N := Finset.mem_Icc.2 ha0
    rw [ite_cond_eq_true _ _ (eq_true ha)]
    have hS : (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ L := by
      have hlast := hall (k - 1) (by omega)
      rw [Nat.cast_sub hk] at hlast
      push_cast at hlast
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · rw [S_reflect]
        have e : a + ((k:ℤ) - 1) * d + ((k:ℤ) - 1) * (-d) = a := by ring
        apply hap _ _ (by omega) (by linarith)
        linarith
      · exact hap a d hpos ha0.1 (by linarith)
    split_ifs <;> linarith
  · push Not at hall
    obtain ⟨j, hj, hjout⟩ := hall
    by_cases hsome : ∃ i < k, 1 ≤ a + i * d ∧ a + i * d ≤ N
    · obtain ⟨i, hi, hin⟩ := hsome
      have hB : a ∈ Finset.Icc (1 - ((k:ℤ) - 1) * |d|) (((k:ℤ) - 1) * |d|) ∪
          Finset.Icc ((N:ℤ) + 1 - ((k:ℤ) - 1) * |d|) (N + ((k:ℤ) - 1) * |d|) := by
        have h1 := abs_le.1 (hbd i hi)
        have h2 := abs_le.1 (hbd j hj)
        simp only [Finset.mem_union, Finset.mem_Icc]
        by_cases hy : 1 ≤ a + j * d
        · right; have := hjout hy; constructor <;> linarith
        · left; constructor <;> linarith
      rw [ite_cond_eq_true _ _ (eq_true hB)]
      have := S_sq_le k N g hsupp hval a d
      split_ifs <;> linarith
    · push Not at hsome
      have h0 : ∑ i ∈ Finset.range k, g (a + i * d) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply hsupp
        by_cases h1 : 1 ≤ a + i * d
        · right; exact hsome i (Finset.mem_range.1 hi) h1
        · left; omega
      rw [h0]
      split_ifs <;> positivity

/-- For a fixed nonzero difference `d` with `|d| ≤ D`, the squared progression sums over a
window add up to at most `N L + 4 k² (k - 1) D`. -/
@[category API, AMS 5 11]
lemma per_d_bound (hk : 1 ≤ k)
    (hap : ∀ a d : ℤ, 0 < d → 1 ≤ a → a + ((k:ℤ) - 1) * d ≤ N →
      (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ L)
    (d M : ℤ) (hd : d ≠ 0) (hdD : |d| ≤ D) :
    ∑ a ∈ Finset.Icc (-M) M, (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤
      N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D := by
  refine (Finset.sum_le_sum
    (fun a _ => S_sq_pointwise k N L g hsupp hval hk hap a d hd)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hk1 : (0:ℤ) ≤ (k:ℤ) - 1 := by
    have : (1:ℤ) ≤ k := (by exact_mod_cast hk)
    linarith
  set K := ((k:ℤ) - 1) * |d| with hK
  have hK0 : 0 ≤ K := mul_nonneg hk1 (abs_nonneg d)
  have c1 : ((Finset.Icc (-M) M ∩ Finset.Icc (1:ℤ) N).card : ℤ) ≤ N := by
    have := Finset.card_le_card
      (Finset.inter_subset_right (s₁ := Finset.Icc (-M) M) (s₂ := Finset.Icc (1:ℤ) N))
    simp at this ⊢; omega
  have c2 : ((Finset.Icc (-M) M ∩
      (Finset.Icc (1 - K) K ∪ Finset.Icc ((N:ℤ) + 1 - K) (N + K))).card : ℤ) ≤ 4 * K := by
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.Icc (-M) M)
      (s₂ := Finset.Icc (1 - K) K ∪ Finset.Icc ((N:ℤ) + 1 - K) (N + K)))
    have h2 := Finset.card_union_le (Finset.Icc (1 - K) K) (Finset.Icc ((N:ℤ) + 1 - K) (N + K))
    simp only [Int.card_Icc] at h1 h2
    omega
  have hKD : K ≤ ((k:ℤ) - 1) * D := mul_le_mul_of_nonneg_left hdD hk1
  have hk2 : (0:ℤ) ≤ (k:ℤ) ^ 2 := by positivity
  have hL : (0:ℤ) ≤ L := by positivity
  nlinarith

omit hval in
/-- The change of variables behind `main_identity`. -/
@[category API, AMS 5 11]
lemma term_shift (M : ℤ) (hM : (N:ℤ) + k * D ≤ M) (i j e e' : ℕ) (hi : i < k) (hj : j < k)
    (he : e < D) (he' : e' < D) :
    ∑ a ∈ Finset.Icc (-M) M, g (a + i * ((e:ℤ) - e')) * g (a + j * ((e:ℤ) - e')) =
      ∑ b ∈ Finset.Icc (-M) M, g (b + ((i:ℤ) - j) * e) * g (b + ((i:ℤ) - j) * e') := by
  have := sum_shift (fun a => g (a + i * ((e:ℤ) - e')) * g (a + j * ((e:ℤ) - e')))
    (1 - i * ((e:ℤ) - e')) (N - i * ((e:ℤ) - e')) M (i * (e':ℤ) - j * e) ?_ ?_ ?_ ?_ ?_
  · rw [← this]
    apply Finset.sum_congr rfl
    intro b _
    congr 2 <;> ring
  · intro x hx
    show g (x + i * ((e:ℤ) - e')) * g (x + j * ((e:ℤ) - e')) = 0
    rw [hsupp (x + i * ((e:ℤ) - e'))
      (by rcases hx with hx | hx <;> [left; right] <;> linarith)]
    simp
  all_goals
    have hi' : (i:ℤ) ≤ k := by exact_mod_cast hi.le
    have hj' : (j:ℤ) ≤ k := by exact_mod_cast hj.le
    have he1 : (e:ℤ) ≤ D := by exact_mod_cast he.le
    have he2 : (e':ℤ) ≤ D := by exact_mod_cast he'.le
    have : (0:ℤ) ≤ N := by positivity
    nlinarith [mul_le_mul hi' he1 (by positivity) (by positivity),
      mul_le_mul hi' he2 (by positivity) (by positivity),
      mul_le_mul hj' he1 (by positivity) (by positivity),
      mul_le_mul hj' he2 (by positivity) (by positivity),
      mul_nonneg (by positivity : (0:ℤ) ≤ i) (by positivity : (0:ℤ) ≤ e),
      mul_nonneg (by positivity : (0:ℤ) ≤ i) (by positivity : (0:ℤ) ≤ e'),
      mul_nonneg (by positivity : (0:ℤ) ≤ j) (by positivity : (0:ℤ) ≤ e),
      mul_nonneg (by positivity : (0:ℤ) ≤ j) (by positivity : (0:ℤ) ≤ e')]

omit hval in
/-- The second-moment identity: summing squared progression sums over all differences
`e - e'` equals a sum of squares indexed by pairs of positions `i, j`. -/
@[category API, AMS 5 11]
lemma main_identity (M : ℤ) (hM : (N:ℤ) + k * D ≤ M) :
    ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D, ∑ a ∈ Finset.Icc (-M) M,
        (∑ i ∈ Finset.range k, g (a + i * ((e:ℤ) - e'))) ^ 2
      = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, ∑ b ∈ Finset.Icc (-M) M,
        (∑ e ∈ Finset.range D, g (b + ((i:ℤ) - j) * e)) ^ 2 := by
  set W := Finset.Icc (-M) M
  simp_rw [sq, Finset.sum_mul_sum]
  calc _ = ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D, ∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.range k, ∑ a ∈ W,
          g (a + i * ((e:ℤ) - e')) * g (a + j * ((e:ℤ) - e')) := by
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun e' _ => ?_))
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D, ∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.range k, ∑ b ∈ W, g (b + ((i:ℤ) - j) * e) * g (b + ((i:ℤ) - j) * e') := by
        refine Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl (fun e' he' => ?_))
        refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
        exact term_shift k D N g hsupp M hM i j e e' (Finset.mem_range.1 hi)
          (Finset.mem_range.1 hj) (Finset.mem_range.1 he) (Finset.mem_range.1 he')
    _ = ∑ e ∈ Finset.range D, ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        ∑ e' ∈ Finset.range D, ∑ b ∈ W, g (b + ((i:ℤ) - j) * e) * g (b + ((i:ℤ) - j) * e') := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, ∑ e ∈ Finset.range D,
        ∑ e' ∈ Finset.range D, ∑ b ∈ W, g (b + ((i:ℤ) - j) * e) * g (b + ((i:ℤ) - j) * e') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        calc _ = ∑ e ∈ Finset.range D, ∑ b ∈ W, ∑ e' ∈ Finset.range D,
              g (b + ((i:ℤ) - j) * e) * g (b + ((i:ℤ) - j) * e') :=
              Finset.sum_congr rfl (fun e _ => Finset.sum_comm)
          _ = _ := Finset.sum_comm

/-- The core inequality: if every `k`-term progression inside `{1,…,N}` has squared signed sum
at most `L`, then `k D² N ≤ D² (N L + 4 k² (k-1) D) + D k² N` for every `D`. -/
@[category API, AMS 5 11]
lemma core_ineq (hk : 1 ≤ k)
    (hap : ∀ a d : ℤ, 0 < d → 1 ≤ a → a + ((k:ℤ) - 1) * d ≤ N →
      (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ L) :
    (k:ℤ) * D ^ 2 * N ≤ D ^ 2 * (N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D) + D * (k ^ 2 * N) := by
  set M : ℤ := (N:ℤ) + k * D
  have hM : (N:ℤ) + k * D ≤ M := le_rfl
  have hMN : (N:ℤ) ≤ M := le_add_of_nonneg_right (by positivity)
  have hid := main_identity k D N g hsupp M hM
  have hk1 : (0:ℤ) ≤ (k:ℤ) - 1 := by
    have : (1:ℤ) ≤ k := (by exact_mod_cast hk)
    linarith
  -- lower bound for the right-hand side
  have hlow : (k:ℤ) * D ^ 2 * N ≤ ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      ∑ b ∈ Finset.Icc (-M) M, (∑ e ∈ Finset.range D, g (b + ((i:ℤ) - j) * e)) ^ 2 := by
    have hdiag : ∀ i ∈ Finset.range k, (D:ℤ) ^ 2 * N ≤ ∑ j ∈ Finset.range k,
        ∑ b ∈ Finset.Icc (-M) M, (∑ e ∈ Finset.range D, g (b + ((i:ℤ) - j) * e)) ^ 2 := by
      intro i hi
      refine le_trans ?_ (Finset.single_le_sum (f := fun j : ℕ => ∑ b ∈ Finset.Icc (-M) M,
        (∑ e ∈ Finset.range D, g (b + ((i:ℤ) - (j:ℤ)) * e)) ^ 2)
        (fun j _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)) hi)
      simp only [sub_self, zero_mul, add_zero, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, sum_sq_g N g hsupp hval M hMN]
    calc (k:ℤ) * D ^ 2 * N = ∑ i ∈ Finset.range k, (D:ℤ) ^ 2 * N := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hdiag
  -- upper bound for the left-hand side
  have hup : ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D, ∑ a ∈ Finset.Icc (-M) M,
        (∑ i ∈ Finset.range k, g (a + i * ((e:ℤ) - e'))) ^ 2 ≤
      ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D,
        ((N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D) + if e = e' then (k:ℤ) ^ 2 * N else 0) := by
    apply Finset.sum_le_sum; intro e he
    apply Finset.sum_le_sum; intro e' he'
    have hB : (0:ℤ) ≤ N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D := by positivity
    by_cases hee : e = e'
    · subst hee
      rw [ite_cond_eq_true _ _ (eq_true rfl)]
      simp only [sub_self, mul_zero, add_zero, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, sum_sq_g N g hsupp hval M hMN]
      linarith
    · rw [ite_cond_eq_false _ _ (eq_false hee), add_zero]
      apply per_d_bound k D N L g hsupp hval hk hap
      · intro h; apply hee; exact_mod_cast (sub_eq_zero.1 h)
      · have := Finset.mem_range.1 he; have := Finset.mem_range.1 he'
        rw [abs_le]; constructor <;> omega
  have hsum : ∑ e ∈ Finset.range D, ∑ e' ∈ Finset.range D,
        ((N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D) + if e = e' then (k:ℤ) ^ 2 * N else 0) =
      D ^ 2 * (N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D) + D * (k ^ 2 * N) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_congr rfl (fun e he => ite_cond_eq_true _ _ (eq_true (Finset.mem_range.1 he)))]
    simp; ring
  linarith

end Core

/-! ### From colourings to the core inequality -/

/-- If `N` is large compared with `k`, `D`, `L` (in the sense of `hN`), and every integer of
absolute value `< ℓ` has square at most `L`, then `APProp k ℓ N` holds. -/
@[category API, AMS 5 11]
theorem apProp_of_ineq (k N L D : ℕ) (ℓ : ℝ) (hk : 1 ≤ k)
    (hℓ : ∀ s : ℤ, |(s : ℝ)| < ℓ → s ^ 2 ≤ L)
    (hN : (D:ℤ) * (N * L + 4 * k ^ 2 * ((k:ℤ) - 1) * D) + k ^ 2 * N < k * D * N) :
    APProp k ℓ N := by
  intro f hf
  by_contra hcon
  push Not at hcon
  set g : ℤ → ℤ := fun x => if 1 ≤ x ∧ x ≤ N then f x.toNat else 0 with hg
  have hsupp : ∀ x, (x < 1 ∨ (N:ℤ) < x) → g x = 0 := by
    intro x hx
    simp only [hg]
    rw [ite_cond_eq_false _ _ (eq_false (by omega))]
  have hval : ∀ x : ℤ, 1 ≤ x → x ≤ N → g x ^ 2 = 1 := by
    intro x h1 h2
    simp only [hg]
    rw [ite_cond_eq_true _ _ (eq_true ⟨h1, h2⟩)]
    rcases hf x.toNat (by omega) (by omega) with h | h <;> rw [h] <;> norm_num
  have hap : ∀ a d : ℤ, 0 < d → 1 ≤ a → a + ((k:ℤ) - 1) * d ≤ N →
      (∑ i ∈ Finset.range k, g (a + i * d)) ^ 2 ≤ L := by
    intro a d hd ha hlast
    have hsum : ∑ i ∈ Finset.range k, g (a + i * d) =
        ∑ i ∈ Finset.range k, f (a.toNat + i * d.toNat) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.1 hi
      have hcast : a + i * d = ((a.toNat + i * d.toNat : ℕ) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      have hid : (i:ℤ) * d ≤ ((k:ℤ) - 1) * d :=
        mul_le_mul_of_nonneg_right (by omega) hd.le
      have hid0 : (0:ℤ) ≤ (i:ℤ) * d := by positivity
      simp only [hg]
      rw [ite_cond_eq_true _ _ (eq_true ⟨by linarith, by linarith⟩), hcast, Int.toNat_natCast]
    rw [hsum]
    apply hℓ
    apply hcon a.toNat d.toNat (by omega) (by omega)
    have : (((k - 1 : ℕ) : ℤ)) = (k:ℤ) - 1 := by rw [Nat.cast_sub hk]; simp
    have h2 : ((a.toNat + (k - 1) * d.toNat : ℕ) : ℤ) = a + ((k:ℤ) - 1) * d := by
      push_cast [this]
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    omega
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; simp at hN; nlinarith [sq_nonneg (k:ℤ), (Nat.cast_nonneg N : (0:ℤ) ≤ N)]
    · exact h
  have := core_ineq k D N L g hsupp hval hk hap
  have hD' : (0:ℤ) < D := by exact_mod_cast hD
  nlinarith

/-! ### The case $\ell = 2$ -/

/-- `k ^ 3 ≤ 4 ^ k` for every natural number `k`. -/
@[category API, AMS 5 11]
lemma cube_le_four_pow (k : ℕ) : k ^ 3 ≤ 4 ^ k := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> norm_num
  · induction k, h using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ 4]
      have : (n + 1) ^ 3 ≤ 4 * n ^ 3 := by
        nlinarith [Nat.mul_le_mul hn hn, Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn]
      omega

/-- For $k \ge 2$, every $\pm 1$-colouring of $\{1, \dots, 50 k^3\}$ has a $k$-term arithmetic
progression with signed sum of absolute value at least $2$. -/
@[category API, AMS 5 11]
theorem apProp_two (k : ℕ) (hk : 2 ≤ k) : APProp k 2 (50 * k ^ 3) := by
  apply apProp_of_ineq k (50 * k ^ 3) 1 (2 * k + 2) 2 (by omega)
  · intro s hs
    have h1 : |s| < 2 := by
      have : ((|s| : ℤ) : ℝ) < 2 := by rw [Int.cast_abs]; exact hs
      exact_mod_cast this
    have h2 : |s| ≤ 1 := by omega
    have h3 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    push_cast
    nlinarith [abs_nonneg s]
  · have hK : (2:ℤ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith [mul_le_mul hK hK (by norm_num) (by positivity),
      pow_le_pow_left₀ (by norm_num) hK 3, pow_le_pow_left₀ (by norm_num) hK 4,
      mul_pos (by positivity : (0:ℤ) < (k:ℤ) ^ 2)
        (by nlinarith : (0:ℤ) < 34 * k ^ 3 - 16 * k ^ 2 - 84 * k + 16)]

/-- $N(k, 2) \le 50 k^3$ for $k \ge 2$. -/
@[category research solved, AMS 5 11]
theorem erdos_176.variants.two_le (k : ℕ) (hk : 2 ≤ k) : erdosN k 2 ≤ 50 * k ^ 3 :=
  Nat.sInf_le (apProp_two k hk)

/-- $N(k, 2)$ is well defined for $k \ge 2$: the defining property holds at $N(k, 2)$. -/
@[category API, AMS 5 11]
theorem apProp_erdosN_two (k : ℕ) (hk : 2 ≤ k) : APProp k 2 (erdosN k 2) :=
  Nat.sInf_mem (s := {N | APProp k 2 N}) ⟨_, apProp_two k hk⟩

/-- For $k = 1$ no $N$ works, so $N(1, 2)$ does not exist. -/
@[category test, AMS 5 11]
theorem not_apProp_one_two (N : ℕ) : ¬ APProp 1 2 N := by
  intro h
  obtain ⟨a, d, -, -, -, hS⟩ := h (fun _ => 1) (fun _ _ _ => Or.inl rfl)
  norm_num at hS

/-- Is there $C > 1$ with $N(k, 2) \le C^k$ for all $k \ge 2$? Yes: $C = 200$ works.

The condition $k \ge 2$ excludes $k = 1$, for which $N(1, 2)$ does not exist. -/
@[category research solved, AMS 5 11]
theorem erdos_176.variants.two : answer(True) ↔
    ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k → (erdosN k 2 : ℝ) ≤ C ^ k := by
  refine iff_of_true trivial ⟨200, by norm_num, fun k hk => ?_⟩
  have h1 : (erdosN k 2 : ℝ) ≤ 50 * (k:ℝ) ^ 3 := by
    exact_mod_cast erdos_176.variants.two_le k hk
  have h2 : (k:ℝ) ^ 3 ≤ 4 ^ k := by exact_mod_cast cube_le_four_pow k
  have h3 : (50:ℝ) ≤ 50 ^ k := by
    calc (50:ℝ) = 50 ^ 1 := by norm_num
      _ ≤ 50 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  calc (erdosN k 2 : ℝ) ≤ 50 * 4 ^ k := by linarith
    _ ≤ 50 ^ k * 4 ^ k := by gcongr
    _ = 200 ^ k := by rw [← mul_pow]; norm_num

/-! ### The case $\ell = c\sqrt{k}$ with $c < 1$ -/

/-- The numerical inequality needed to apply `apProp_of_ineq` with $\ell = c\sqrt{k}$. -/
@[category API, AMS 5 11]
lemma sqrt_ineq_aux (c : ℝ) (hc1 : c < 1) (hc0 : 0 ≤ c) (k m L : ℕ) (hk : 1 ≤ k)
    (hm : 2 / (1 - c ^ 2) ≤ (m:ℝ)) (hL : (L:ℝ) ≤ c ^ 2 * k) :
    ((k * m : ℕ) : ℤ) * ((4 * m ^ 2 * k ^ 3 : ℕ) * L + 4 * k ^ 2 * ((k:ℤ) - 1) * (k * m : ℕ)) +
      k ^ 2 * (4 * m ^ 2 * k ^ 3 : ℕ) < k * (k * m : ℕ) * (4 * m ^ 2 * k ^ 3 : ℕ) := by
  have h1c : 0 < 1 - c ^ 2 := by nlinarith
  have hm2 : 2 ≤ (m:ℝ) * (1 - c ^ 2) := by rwa [div_le_iff₀ h1c] at hm
  have hmpos : (0:ℝ) < m := by
    have : (0:ℝ) < 2 / (1 - c ^ 2) := by positivity
    linarith
  have hK : (1:ℝ) ≤ k := by exact_mod_cast hk
  suffices H : ((k:ℝ) * m) * ((4 * m ^ 2 * k ^ 3) * L + 4 * k ^ 2 * ((k:ℝ) - 1) * (k * m)) +
      k ^ 2 * (4 * m ^ 2 * k ^ 3) < k * (k * m) * (4 * m ^ 2 * k ^ 3) by
    exact_mod_cast H
  set D : ℝ := k * m with hD
  set N : ℝ := 4 * m ^ 2 * k ^ 3 with hN
  have hDN : (0:ℝ) ≤ D * N := by positivity
  have step1 : D * (N * L) ≤ D * N * (c ^ 2 * k) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hL hDN
  have step2 : (k:ℝ) * D * N - D * N * (c ^ 2 * k) - k ^ 2 * N ≥ N * k ^ 2 := by
    have : (0:ℝ) ≤ N * k ^ 2 := by positivity
    have e : (k:ℝ) * D * N - D * N * (c ^ 2 * k) - k ^ 2 * N =
        N * k ^ 2 * (m * (1 - c ^ 2) - 1) := by
      rw [hD]; ring
    rw [e]; nlinarith
  have step3 : D * (4 * k ^ 2 * ((k:ℝ) - 1) * D) < N * k ^ 2 := by
    have : (0:ℝ) < m ^ 2 * k ^ 4 := by positivity
    have e : D * (4 * k ^ 2 * ((k:ℝ) - 1) * D) = 4 * m ^ 2 * k ^ 4 * (k - 1) := by
      rw [hD]; ring
    have e2 : N * k ^ 2 = 4 * m ^ 2 * k ^ 4 * k := by rw [hN]; ring
    rw [e, e2]; nlinarith
  nlinarith

/-- For $0 \le c < 1$ and $k \ge 1$, with $m = \lceil 2 / (1 - c^2) \rceil$, every
$\pm 1$-colouring of $\{1, \dots, 4 m^2 k^3\}$ has a $k$-term arithmetic progression with signed
sum of absolute value at least $c \sqrt{k}$. -/
@[category API, AMS 5 11]
theorem apProp_sqrt (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (k : ℕ) (hk : 1 ≤ k) :
    APProp k (c * √(k:ℝ)) (4 * ⌈2 / (1 - c ^ 2)⌉₊ ^ 2 * k ^ 3) := by
  apply apProp_of_ineq k _ ⌊c ^ 2 * k⌋₊ (k * ⌈2 / (1 - c ^ 2)⌉₊) _ hk
  · intro s hs
    have hx : 0 ≤ c ^ 2 * k := by positivity
    have h1 : ((s ^ 2 : ℤ) : ℝ) < c ^ 2 * k := by
      have h0 : 0 ≤ |(s:ℝ)| := abs_nonneg _
      have hsq : (c * √(k:ℝ)) ^ 2 = c ^ 2 * k := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      push_cast
      rw [← sq_abs, ← hsq]
      exact pow_lt_pow_left₀ hs h0 (by norm_num)
    rw [Int.natCast_floor_eq_floor hx]
    exact Int.le_floor.2 h1.le
  · exact sqrt_ineq_aux c hc1 hc0 k _ _ hk (Nat.le_ceil _) (Nat.floor_le (by positivity))

/-- $N(k, c\sqrt{k}) \le 4 \lceil 2/(1-c^2) \rceil^2 k^3$ for $0 \le c < 1$ and $k \ge 1$. -/
@[category research solved, AMS 5 11]
theorem erdos_176.variants.sqrt_mul_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (k : ℕ)
    (hk : 1 ≤ k) : erdosN k (c * √(k:ℝ)) ≤ 4 * ⌈2 / (1 - c ^ 2)⌉₊ ^ 2 * k ^ 3 :=
  Nat.sInf_le (apProp_sqrt c hc0 hc1 k hk)

/-- For every fixed $0 \le c < 1$ there is $C > 1$ with $N(k, c\sqrt{k}) \le C^k$ for all
$k \ge 1$. -/
@[category research solved, AMS 5 11]
theorem erdos_176.variants.sqrt_mul (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k → (erdosN k (c * √(k:ℝ)) : ℝ) ≤ C ^ k := by
  set m := ⌈2 / (1 - c ^ 2)⌉₊ with hm
  have h1c : 0 < 1 - c ^ 2 := by nlinarith
  have hm1 : (1:ℝ) ≤ m := by
    have h2 : 2 / (1 - c ^ 2) ≤ (m:ℝ) := Nat.le_ceil _
    have h3 : (2:ℝ) ≤ 2 / (1 - c ^ 2) := by
      rw [le_div_iff₀ h1c]; nlinarith
    linarith
  refine ⟨16 * m ^ 2, by nlinarith, fun k hk => ?_⟩
  have h1 : (erdosN k (c * √(k:ℝ)) : ℝ) ≤ 4 * (m:ℝ) ^ 2 * (k:ℝ) ^ 3 := by
    exact_mod_cast erdos_176.variants.sqrt_mul_le c hc0 hc1 k hk
  have h2 : (k:ℝ) ^ 3 ≤ 4 ^ k := by exact_mod_cast cube_le_four_pow k
  have h3 : 4 * (m:ℝ) ^ 2 ≤ (4 * (m:ℝ) ^ 2) ^ k := by
    calc 4 * (m:ℝ) ^ 2 = (4 * (m:ℝ) ^ 2) ^ 1 := by norm_num
      _ ≤ (4 * (m:ℝ) ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith) (by omega)
  calc (erdosN k (c * √(k:ℝ)) : ℝ) ≤ 4 * (m:ℝ) ^ 2 * 4 ^ k := by
        have : 0 ≤ 4 * (m:ℝ) ^ 2 := by positivity
        nlinarith
    _ ≤ (4 * (m:ℝ) ^ 2) ^ k * 4 ^ k := by gcongr
    _ = (16 * m ^ 2) ^ k := by rw [← mul_pow]; ring

end Erdos176

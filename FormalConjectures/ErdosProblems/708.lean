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
# Erdős Problem 708

*References:*
- [erdosproblems.com/708](https://www.erdosproblems.com/708)
- [ErSu59] Erdős, Pál and Surányi, János, *Megjegyzések egy versenyfeladathoz* (*Bemerkungen zu
  einer Aufgabe eines mathematischen Wettbewerbs*). Mat. Lapok 10 (1959), 39–48.
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Le Matematiche (Catania) 47 (1992), 231–240.
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy–Ramanujan J. 15
  (1992), 34–50.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44–48.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas 2 (1995), 165–186.
- [Ch26] Chen, Haoyu, *Explicit upper bounds for the Erdős–Surányi function $g(n)$*. Zenodo
  preprint (2026). [doi:10.5281/zenodo.22660853](https://doi.org/10.5281/zenodo.22660853)
- [Be26a] Bergström, C., *Exact Small-$n$ Values ($g(4) = 5$, $g(5) = 6$, $g(6) = 8$) and
  Constructive Lower Bounds ($g(7) \ge 9$, $g(8) \ge 11$) for Erdős Problem 708*. Zenodo preprint
  (2026). [doi:10.5281/zenodo.24366897](https://doi.org/10.5281/zenodo.24366897)
- [Be26b] Bergström, C., *Whole-Cofactor Peeling, Extreme-Point LP Rank Rounding, and
  Shifted-Interval Hinge Duality for Erdős Problem 708*. Zenodo preprint (2026).
  [doi:10.5281/zenodo.24342717](https://doi.org/10.5281/zenodo.24342717)
- [Be26c] Bergström, C., *Lean 4 Formalization and Verification Suite for Scaled-Interval Hinge
  Telescoping, Difference-of-Convex Obstructions, and Smooth Proper-Divisor Matching for Erdős
  Problem 708*. Zenodo (2026).
  [doi:10.5281/zenodo.24366998](https://doi.org/10.5281/zenodo.24366998)
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace Erdos708

/-- The block $\{x + 1, \dots, x + L\}$ of `length` consecutive positive integers after `start`. -/
def window (start length : ℕ) : Finset ℕ := Finset.Icc (start + 1) (start + length)

/-- `HasProductCover A start k` states that the window of $\max(A)$ consecutive positive integers
after `start` contains a subset $B$ of size at most $k$ whose product is divisible by
$\prod_{a \in A} a$. Writing $|B| \le k$ makes the predicate upward closed in $k$ and handles
short windows such as $A = \{2, \dots, n + 1\}$ where $\max(A) = n + 1 < g(n)$. -/
def HasProductCover (A : Finset ℕ) (start k : ℕ) : Prop :=
  ∃ B : Finset ℕ, B ⊆ window start (A.sup id) ∧ B.card ≤ k ∧
    (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

/-- `HasCoveringSize n k` states that every $n$-element subset $A \subseteq [2, \infty)$ of
natural numbers and every starting offset `start` admit a product cover of size at most `k`.
Restricting to positive windows matches [Er92c] without changing $g(n)$, since any window in
$\mathbb{Z}$ containing $0$ is covered by $\{0\}$ and negative windows reflect via $b \mapsto -b$.
-/
def HasCoveringSize (n k : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) → ∀ start : ℕ,
    HasProductCover A start k

/-- The Erdős–Surányi function $g(n)$: the minimal $k$ such that every $n$-element subset
$A \subseteq [2, \infty) \cap \mathbb{N}$ and every block $I$ of $\max(A)$ consecutive positive
integers admit $B \subseteq I$ with $|B| \le k$ and $\prod_{a \in A} a \mid \prod_{b \in B} b$.
Nonemptiness of $\{k : \mathbb{N} \mid \text{HasCoveringSize } n\ k\}$ holds by [Ch26]
(`erdos_708.variants.chen_twelve_n`), so `sInf` is the true minimum (`g 0 = 0`). -/
noncomputable def g (n : ℕ) : ℕ := sInf {k : ℕ | HasCoveringSize n k}

/-- Product covers are monotone in the allowed subset size `k`. -/
@[category API, AMS 11]
theorem hasProductCover_mono {A : Finset ℕ} {start k l : ℕ} (hkl : k ≤ l)
    (h : HasProductCover A start k) : HasProductCover A start l := by
  obtain ⟨B, hsub, hcard, hdvd⟩ := h
  exact ⟨B, hsub, hcard.trans hkl, hdvd⟩

/-- Uniform covering size is monotone in `k`. -/
@[category API, AMS 11]
theorem hasCoveringSize_mono {n k l : ℕ} (hkl : k ≤ l) (h : HasCoveringSize n k) :
    HasCoveringSize n l :=
  fun A hcard htwo start ↦ hasProductCover_mono hkl (h A hcard htwo start)

/-- Every window of `M` consecutive positive integers contains a multiple of `a` (`0 < a ≤ M`). -/
@[category API, AMS 11]
theorem exists_multiple_in_window {a M start : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    ∃ b ∈ window start M, a ∣ b := by
  let b := a * (start / a) + a
  have hmod := Nat.mod_lt start ha
  have hdiv := Nat.div_add_mod start a
  refine ⟨b, Finset.mem_Icc.2 ⟨by dsimp [b]; omega, by dsimp [b]; omega⟩, ?_⟩
  exact ⟨start / a + 1, by dsimp [b]; ring⟩

/-- Every window of `M` consecutive positive integers contains two distinct multiples of `d` when
`0 < d` and `2 * d ≤ M`. -/
@[category API, AMS 11]
theorem two_multiples_in_window {d M start : ℕ} (hd : 0 < d) (hdM : 2 * d ≤ M) :
    ∃ b₁ ∈ window start M, ∃ b₂ ∈ window start M,
      b₁ ≠ b₂ ∧ d ∣ b₁ ∧ d ∣ b₂ := by
  let b₁ := d * (start / d) + d
  let b₂ := d * (start / d) + 2 * d
  have hmod := Nat.mod_lt start hd
  have hdiv := Nat.div_add_mod start d
  refine ⟨b₁, Finset.mem_Icc.2 ⟨by dsimp [b₁]; omega, by dsimp [b₁]; omega⟩,
    b₂, Finset.mem_Icc.2 ⟨by dsimp [b₂]; omega, by dsimp [b₂]; omega⟩,
    by dsimp [b₁, b₂]; omega, ⟨start / d + 1, by dsimp [b₁]; ring⟩,
    ⟨start / d + 2, by dsimp [b₂]; ring⟩⟩

/-- Sanity check at $n = 0$: the empty input has $g(0) = 0$. -/
@[category test, AMS 11]
theorem g_zero : g 0 = 0 := by
  have h0 : HasCoveringSize 0 0 := fun A hcard _ _ ↦ by
    rw [Finset.card_eq_zero.1 hcard]
    exact ⟨∅, Finset.empty_subset _, le_rfl, by simp⟩
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le h0)

/-- Sanity check at $n = 1$: $g(1) = 1$. -/
@[category test, AMS 11]
theorem g_one : g 1 = 1 := by
  have h1 : HasCoveringSize 1 1 := fun A hcard htwo start ↦ by
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hcard
    have ha2 : 2 ≤ a := htwo a (Finset.mem_singleton_self a)
    obtain ⟨b, hb, hdvd⟩ :=
      exists_multiple_in_window (M := a) (start := start) (by omega) le_rfl
    exact ⟨{b}, by simpa [Finset.singleton_subset_iff] using hb, by simp,
      by simpa using hdvd⟩
  refine IsLeast.csInf_eq ⟨h1, fun k hk ↦ ?_⟩
  obtain ⟨B, _, hcard, hdvd⟩ := hk {2} (by simp) (by simp) 0
  by_contra hlt
  have hB : B = ∅ := Finset.card_eq_zero.1 (by omega)
  subst hB
  simp at hdvd

/-- Any two-element set $\{a, M\}$ with $2 \le a < M$ admits a product cover of size at most $2$
in every window of length $M$ (Gallai [ErSu59]). -/
@[category API, AMS 11]
theorem hasProductCover_pair {a M : ℕ} (ha : 2 ≤ a) (haM : a < M) (start : ℕ) :
    HasProductCover {a, M} start 2 := by
  have hsup : ({a, M} : Finset ℕ).sup id = M := le_antisymm
    (Finset.sup_le fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haM.le
      · exact le_rfl)
    (Finset.le_sup (f := id) (by simp))
  obtain ⟨b₁, hb₁, hMb₁⟩ :=
    exists_multiple_in_window (a := M) (M := M) (start := start) (by omega) le_rfl
  obtain ⟨m, hm, ham⟩ :=
    exists_multiple_in_window (a := a) (M := M) (start := start) (by omega) haM.le
  by_cases hmb : m = b₁
  · rw [hmb] at ham
    have h2d : 2 * Nat.gcd a M ≤ M := by
      have hd_le := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a M)
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_right a M
      rcases k with _ | _ | k
      · omega
      · omega
      · have hexp : Nat.gcd a M * (k + 1 + 1) = Nat.gcd a M * k + 2 * Nat.gcd a M := by ring
        omega
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, hdc₁, hdc₂⟩ := two_multiples_in_window
      (start := start) (Nat.gcd_pos_of_pos_left M (by omega)) h2d
    let b₂ := if c₁ = b₁ then c₂ else c₁
    have hb₂ : b₂ ∈ window start M := by dsimp [b₂]; split_ifs <;> assumption
    have hne₂ : b₂ ≠ b₁ := by dsimp [b₂]; split_ifs <;> omega
    have hdb₂ : Nat.gcd a M ∣ b₂ := by dsimp [b₂]; split_ifs <;> assumption
    refine ⟨{b₂, b₁}, fun x hx ↦ ?_, Finset.card_insert_le b₂ {b₁}, ?_⟩
    · rw [hsup]; simp at hx; rcases hx with rfl | rfl <;> assumption
    · rw [Finset.prod_pair haM.ne, Finset.prod_pair hne₂]
      have hgcd : a * M ∣ Nat.gcd a M * b₁ := by
        rw [← Nat.gcd_mul_right]
        exact Nat.dvd_gcd (Nat.mul_dvd_mul_left a hMb₁)
          (mul_comm M a ▸ Nat.mul_dvd_mul_left M ham)
      exact dvd_trans hgcd (Nat.mul_dvd_mul_right hdb₂ b₁)
  · refine ⟨{m, b₁}, fun x hx ↦ ?_, Finset.card_insert_le m {b₁}, ?_⟩
    · rw [hsup]; simp at hx; rcases hx with rfl | rfl <;> assumption
    · rw [Finset.prod_pair haM.ne, Finset.prod_pair hmb]; exact mul_dvd_mul ham hMb₁

/-- Gallai observed that $g(2) = 2$ [ErSu59]: every window of length $\max(a, b)$ covers $ab$ in
at most two elements, whereas $A = \{2, 3\}$ on $\{2, 3, 4\}$ has no single multiple of $6$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_two : g 2 = 2 := by
  have h2 : HasCoveringSize 2 2 := fun A hcard htwo start ↦ by
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 hcard
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · exact hasProductCover_pair (htwo u (by simp)) hlt start
    · exact absurd rfl huv
    · rw [Finset.pair_comm]; exact hasProductCover_pair (htwo v (by simp)) hgt start
  refine IsLeast.csInf_eq ⟨h2, fun k hk ↦ ?_⟩
  obtain ⟨B, hBsub, hcard, hdvd⟩ := hk {2, 3} (by decide) (by decide) 1
  by_contra hlt
  have hsup : ({2, 3} : Finset ℕ).sup id = 3 := by decide
  rw [show (∏ a ∈ ({2, 3} : Finset ℕ), a) = 6 from by decide] at hdvd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by omega : B.card ≤ 1) with h0 | h1
  · rw [Finset.card_eq_zero.1 h0] at hdvd; norm_num at hdvd
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 h1
    have hb := hBsub (Finset.mem_singleton_self b)
    rw [hsup] at hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.1 hb
    have h6b : 6 ∣ b := by simpa using hdvd
    omega

/--
Let $g(n)$ be minimal such that for any $A \subseteq [2, \infty) \cap \mathbb{N}$ with $|A| = n$
and any set $I$ of $\max(A)$ consecutive positive integers there exists some $B \subseteq I$ with
$|B| \le g(n)$ such that
$$\prod_{a \in A} a \mid \prod_{b \in B} b.$$
Is it true that $g(n) \le (2 + o(1)) n$?

See also [709](https://www.erdosproblems.com/709).
-/
@[category research open, question, AMS 11]
theorem erdos_708 :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (2 + ε) * (n : ℝ) := by
  sorry

/-- Or perhaps even $g(n) \le 2n$ for every $n$? -/
@[category research open, question, AMS 11]
theorem erdos_708.variants.two_n : ∀ n : ℕ, g n ≤ 2 * n := by
  sorry

/-- Combined with $g(n) \ge (2 - o(1)) n$ [ErSu59], a positive answer to `erdos_708` is equivalent
to the asymptotic formula $g(n) \sim 2n$. -/
@[category research open, AMS 11]
theorem erdos_708.variants.asymptotic :
    (fun n : ℕ ↦ (g n : ℝ)) ~[atTop] fun n : ℕ ↦ 2 * (n : ℝ) := by
  sorry

/-- Erdős and Surányi [ErSu59] proved that $g(n) \ge (2 - o(1)) n$, taking $A$ as the set of
semiprimes $p_i p_j$ ($1 \le i < j \le \ell$) for primes $p_1 < \dots < p_\ell$ with
$p_\ell^2 < 2 p_1^2$ around a common multiple of $p_1 \cdots p_\ell$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.lower_bound :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 - ε) * (n : ℝ) ≤ (g n : ℝ) := by
  sorry

/-- Chen [Ch26] (`doi:10.5281/zenodo.22660853`) proved the uniform linear upper bound
$g(n) \le 12n$ for all $n$ (formalised in Lean 4) and $g(n) \le 11n$ via LP hinge duality. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.chen_twelve_n (n : ℕ) : HasCoveringSize n (12 * n) := by
  sorry

/-- Any obstruction `¬ HasCoveringSize n k` implies `k + 1 ≤ g n`. -/
@[category API, AMS 11]
theorem le_g_of_not_hasCoveringSize {n k : ℕ} (h : ¬ HasCoveringSize n k) : k + 1 ≤ g n := by
  refine le_csInf ⟨12 * n, erdos_708.variants.chen_twelve_n n⟩ fun m hm ↦ ?_
  by_contra hlt
  exact h (hasCoveringSize_mono (by omega) hm)

/-- Bergström [Be26b, Be26c] (`doi:10.5281/zenodo.24342717`, `doi:10.5281/zenodo.24366998`),
combining whole-cofactor cumulative-GCD peeling and smooth extreme-point LP rank rounding with
shifted-interval hinge duality, proved $g(n) \le (56501 / 6400 + o(1)) n$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.bergstrom_asymptotic :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ (56501 / 6400 + ε) * (n : ℝ) := by
  sorry

/-- Explicit finite-threshold bound from [Be26b] (`doi:10.5281/zenodo.24342717`): $g(n) \le 10n$
holds unconditionally for all $n \ge 1446$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.bergstrom_ten_n (n : ℕ) (hn : 1446 ≤ n) : g n ≤ 10 * n := by
  sorry

/-- Erdős and Surányi [ErSu59] proved that $g(3) = 4$ (Gallai had observed $g(3) \ge 4$). -/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_three : g 3 = 4 := by
  sorry

/-- Bergström [Be26a] (`doi:10.5281/zenodo.24366897`) proved $g(4) = 5$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_four : g 4 = 5 := by
  sorry

/-- Bergström [Be26a] (`doi:10.5281/zenodo.24366897`) proved $g(5) = 6$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_five : g 5 = 6 := by
  sorry

/-- Bergström [Be26a] (`doi:10.5281/zenodo.24366897`) proved $g(6) = 8$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.g_six : g 6 = 8 := by
  sorry

/-- Bergström [Be26a, Proposition 4] (`doi:10.5281/zenodo.24366897`) proved $g(7) \ge 9$ via the
witness $(\{41, 43, 47, 53\} \times \{59, 61\}) \setminus \{2419\}$ at $M = 3233$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.nine_le_g_seven : 9 ≤ g 7 := by
  sorry

/-- Bergström [Be26a, Proposition 4] (`doi:10.5281/zenodo.24366897`) proved $g(8) \ge 11$ via the
bipartite semiprime witness $\{41, 43, 47, 53\} \times \{59, 61\}$ at $M = 3233$. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.eleven_le_g_eight : 11 ≤ g 8 := by
  sorry

/- ## Five-prime M = 65231 difference-of-convex hinge counterexample -/

/-- The five active primes $P_5 = \{29, 31, 37, 41, 43\}$ of [Be26c, Proposition 3]. -/
def P5 : Finset ℕ := {29, 31, 37, 41, 43}

/-- Window length $M_5 = 37 \cdot 41 \cdot 43 = 65231$ and shift $x_5$ of [Be26c, Proposition 3]. -/
def M5 : ℕ := 65231

/-- Chinese Remainder shift $x_5 = 6697389240194279945569557312011$ of [Be26c, Proposition 3]. -/
def x5 : ℕ := 6697389240194279945569557312011

/-- Exact $p$-adic valuation on integers not divisible by $p^4$. -/
def vp3 (p n : ℕ) : ℕ :=
  (if p ∣ n then 1 else 0) + (if p ^ 2 ∣ n then 1 else 0) + (if p ^ 3 ∣ n then 1 else 0)

/-- Integer-scaled prime-weighted valuation $X_w(n) = \sum_{p \in P_5} v_p(n) w(p)$. -/
def weightedVal5 (w : ℕ → ℕ) (n : ℕ) : ℕ := ∑ p ∈ P5, vp3 p n * w p

/-- Scaled left-hand hinge sum $\sum_{m = 1}^{M_5} (X_w(m) - C)_+$ (`C = 106` for $c = 1.06$). -/
def hingeLhs5 (C : ℕ) (w : ℕ → ℕ) : ℕ := ∑ m ∈ window 0 M5, (weightedVal5 w m - C)

/-- Scaled right-hand hinge sum $\sum_{b \in I_{x_5}} (X_w(b) - D)_+$ (`D = 100` for $1.00$). -/
def hingeRhs5 (D : ℕ) (w : ℕ → ℕ) : ℕ := ∑ b ∈ window x5 M5, (weightedVal5 w b - D)

/-- Binary vertex weight assignment $w_S \in \{0, 100\}^{P_5}$ indexed by `mask : Fin 32`. -/
def binWeight5 (mask : Fin 32) (p : ℕ) : ℕ :=
  if p = 29 then if mask.val.testBit 0 then 100 else 0
  else if p = 31 then if mask.val.testBit 1 then 100 else 0
  else if p = 37 then if mask.val.testBit 2 then 100 else 0
  else if p = 41 then if mask.val.testBit 3 then 100 else 0
  else if p = 43 then if mask.val.testBit 4 then 100 else 0
  else 0

/-- The $35$ three-prime products from $P_5 = \{29, 31, 37, 41, 43\}$ with multiplicity. -/
def Q35 : Finset ℕ :=
  {24389, 26071, 27869, 29791, 31117, 33263, 34481, 35557, 36163, 36859, 38657, 39401,
   39701, 41323, 42439, 43993, 46139, 47027, 48749, 49321, 50653, 51127, 52111, 53621,
   54653, 56129, 57319, 58867, 62197, 65231, 68413, 68921, 72283, 75809, 79507}

/-- Closed-form midpoint tally on `Q35` verifying the $1540$ vs $1450$ ($+90$) interior hinge
violation at $w_* = (50, 50, 50, 50, 50)$. -/
@[category test, AMS 11]
theorem midpoint_hinge_closed_form_65231 :
    (∑ q ∈ Q35, 44 * (M5 / q)) = 1540 ∧
      (∑ q ∈ Q35, 50 * ((x5 + M5) / q - x5 / q)) - 350 = 1450 ∧
      weightedVal5 (fun _ ↦ 50) (x5 + 32616) - 100 = 150 := by
  decide

/-- Bergström [Be26c, Proposition 3] (`doi:10.5281/zenodo.24366998`): on
$P_5 = \{29, 31, 37, 41, 43\}$ at $M_5 = 65231$ and $x_5 = 6697389240194279945569557312011$, the
shifted-interval hinge inequality $(H_{1.06})$ (scaled by $100$) holds on all $32$ binary vertices
$w \in \{0, 100\}^{P_5}$, yet fails at the interior midpoint $w_* = (50, 50, 50, 50, 50)$ by $+90$
($+0.90$ unscaled: $1540 = 1450 + 90$), refuting binary extreme-point reduction for the
difference-of-convex hinge functional. -/
@[category research solved, AMS 11]
theorem erdos_708.variants.dc_hinge_counterexample_65231 :
    (∀ mask : Fin 32, hingeLhs5 106 (binWeight5 mask) ≤ hingeRhs5 100 (binWeight5 mask)) ∧
      hingeRhs5 100 (fun _ ↦ 50) + 90 ≤ hingeLhs5 106 (fun _ ↦ 50) := by
  sorry

end Erdos708

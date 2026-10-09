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
# Erdős Problem 374

*References:*
- [erdosproblems.com/374](https://www.erdosproblems.com/374)
- [ErGr76] Erdős, P. and Graham, R. L., On products of factorials.
  Bull. Inst. Math. Acad. Sinica (1976), 337–355.
- [LSS14] Luca, F. and Saradha, N. and Shorey, T. N., Squares and factorials in
  products of factorials. Monatsh. Math. (2014), 385–400.
-/
@[expose] public section

namespace Erdos374

open scoped BigOperators

/-- A square product of exactly $k$ distinct positive factorial arguments with maximum $m$. -/
def HasRepresentation (m k : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ m ∈ s ∧
    (∀ a ∈ s, 0 < a ∧ a ≤ m) ∧ IsSquare (∏ a ∈ s, Nat.factorial a)

/-- The endpoint $m$ has minimum representation cardinality $k \geq 2$. -/
def HasMinimum (m k : ℕ) : Prop :=
  2 ≤ k ∧ HasRepresentation m k ∧ ∀ j, 2 ≤ j → j < k → ¬ HasRepresentation m j

/-- The endpoints with minimum representation cardinality $k$. -/
def D (k : ℕ) : Set ℕ := {m | HasMinimum m k}

/-- The number of elements of $D_k$ in $\{1,\ldots,n\}$. -/
noncomputable def countD (k n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun m => HasMinimum m k)).card

/-- The set $D_6$ has positive lower density. -/
def PositiveLowerDensitySix : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) ≤ (countD 6 n : ℝ)

@[category API, AMS 11]
theorem rep_two {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsq : IsSquare (Nat.factorial a * Nat.factorial b)) : HasRepresentation b 2 := by
  refine ⟨{a, b}, ?_, by simp, ?_, ?_⟩
  · simp [ne_of_lt hab]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  · simpa [Finset.prod_pair, ne_of_lt hab] using hsq

/-- Classical adjacent-factor construction for every square greater than one. -/
@[category API, AMS 11]
theorem square_hasMinimum_two {r : ℕ} (hr : 1 < r) : HasMinimum (r ^ 2) 2 := by
  have hn : 0 < r ^ 2 := by positivity
  have hpred : 0 < r ^ 2 - 1 := by
    have : 1 < r ^ 2 := by nlinarith
    omega
  refine ⟨le_rfl, rep_two hpred (by omega) ?_, ?_⟩
  · refine ⟨r * Nat.factorial (r ^ 2 - 1), ?_⟩
    rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn)]
    ring
  · intro j hj hlt
    omega

/-- Two consecutive factorials expose exactly one unsquared factor. -/
@[category API, AMS 11]
theorem adjacent_identity {n : ℕ} (hn : 0 < n) :
    Nat.factorial n * Nat.factorial (n - 1) =
      n * Nat.factorial (n - 1) ^ 2 := by
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn)]
  ring

/-- The classical four-factor identity; distinctness is a separate obligation. -/
@[category API, AMS 11]
theorem four_factor_identity {r u : ℕ} (hr : 0 < r) (hu : 0 < u) :
    Nat.factorial (r ^ 2 * u) * Nat.factorial (r ^ 2 * u - 1) *
      Nat.factorial u * Nat.factorial (u - 1) =
      (r * u * Nat.factorial (r ^ 2 * u - 1) * Nat.factorial (u - 1)) ^ 2 := by
  have hn : 0 < r ^ 2 * u := by positivity
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt hu)]
  ring

/-- Erdős--Graham six-factor identity; it does not exclude shorter representations. -/
@[category API, AMS 11]
theorem six_factor_identity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.factorial (a * b) * Nat.factorial (a * b - 1) *
      Nat.factorial a * Nat.factorial (a - 1) *
      Nat.factorial b * Nat.factorial (b - 1) =
      (a * b * Nat.factorial (a * b - 1) *
        Nat.factorial (a - 1) * Nat.factorial (b - 1)) ^ 2 := by
  have hn : 0 < a * b := Nat.mul_pos ha hb
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt ha),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt hb)]
  ring

/-- A fixed m cannot have two different minimum cardinalities. -/
@[category API, AMS 11]
theorem minimum_unique {m k l : ℕ} (hk : HasMinimum m k) (hl : HasMinimum m l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (hl.2.2 k hk.1 h hk.2.1)
  · exact h
  · exact False.elim (hk.2.2 l hl.1 h hl.2.1)

/-- No $D_k$ contains a prime. Studied by Erdős and Graham [ErGr76]. -/
@[category research solved, AMS 11]
theorem erdos_374.variants.prime_no_rep {p k : ℕ} (hp : Nat.Prime p) : ¬ HasRepresentation p k := by
  classical
  rintro ⟨s, hk, hps, hbound, hsquare⟩
  have hfactor : p.factorial = p * (p - 1).factorial := by
    have hsucc : p - 1 + 1 = p := by have := hp.two_le; omega
    simpa only [hsucc] using Nat.factorial_succ (p - 1)
  have hrest : ¬ p ∣ ∏ a ∈ s.erase p, a.factorial := by
    have hgeneral : ∀ t : Finset ℕ, (∀ a ∈ t, a < p) → ¬ p ∣ ∏ a ∈ t, a.factorial := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [hp.ne_one]
      | @insert a t hat ih =>
        intro hb
        rw [Finset.prod_insert hat]
        apply hp.not_dvd_mul
        · intro hd
          have := hp.dvd_factorial.mp hd
          have := hb a (Finset.mem_insert_self a t)
          omega
        · apply ih
          intro b hbt
          exact hb b (Finset.mem_insert_of_mem hbt)
    apply hgeneral
    intro a ha
    have hmem := Finset.mem_erase.mp ha
    have := (hbound a hmem.2).2
    omega
  have hprevious : ¬ p ∣ (p - 1).factorial := by
    intro hd
    have := hp.dvd_factorial.mp hd
    have := hp.two_le
    omega
  let t := (p - 1).factorial * ∏ a ∈ s.erase p, a.factorial
  have ht : ¬ p ∣ t := hp.not_dvd_mul hprevious hrest
  have hprod : ∏ a ∈ s, a.factorial = p * t := by
    rw [← Finset.mul_prod_erase s Nat.factorial hps, hfactor]
    simp [t, mul_assoc]
  obtain ⟨x, hx⟩ := hsquare
  have heq : p * t = x * x := by simpa [hprod] using hx
  have hpx : p ∣ x := by
    have hdiv : p ∣ x * x := by rw [← heq]; exact Nat.dvd_mul_right p t
    exact (hp.dvd_mul.mp hdiv).elim id id
  obtain ⟨y, hy⟩ := hpx
  have heq2 : p * t = p * (p * (y * y)) := by
    rw [heq, hy]
    ring
  have htEq : t = p * (y * y) := Nat.mul_left_cancel hp.pos heq2
  exact ht (htEq ▸ Nat.dvd_mul_right p (y * y))

@[category API, AMS 11]
theorem product_separated_rep_six {a b : ℕ} (ha : 2 ≤ a) (hab : a + 2 ≤ b) : HasRepresentation (a * b) 6 := by
  have hb : 2 ≤ b := by omega
  have han0 : a + 2 ≤ a * b := by nlinarith
  have hbn0 : b + 2 ≤ a * b := by nlinarith
  have han : a < a * b - 1 := by omega
  have hbn : b < a * b - 1 := by omega
  have hne : a * b - 1 < a * b := by omega
  have h1 : 0 < a - 1 := by omega
  have h2 : a - 1 < a := by omega
  have h3 : a < b - 1 := by omega
  have h4 : b - 1 < b := by omega
  refine ⟨{a - 1,a,b - 1,b,a * b - 1,a * b}, ?_, by simp, ?_, ?_⟩
  · simp [show a - 1 ≠ a by omega, show a - 1 ≠ b - 1 by omega,
      show a - 1 ≠ b by omega, show a - 1 ≠ a * b - 1 by omega,
      show a - 1 ≠ a * b by omega, show a ≠ b - 1 by omega,
      show a ≠ b by omega, show a ≠ a * b - 1 by omega,
      show a ≠ a * b by omega, show b - 1 ≠ b by omega,
      show b - 1 ≠ a * b - 1 by omega, show b - 1 ≠ a * b by omega,
      show b ≠ a * b - 1 by omega, show b ≠ a * b by omega,
      show a * b - 1 ≠ a * b by omega]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have hprod : (∏ x ∈ ({a - 1,a,b - 1,b,a * b - 1,a * b} : Finset ℕ), x.factorial) =
        (a - 1).factorial * a.factorial * (b - 1).factorial * b.factorial * (a * b - 1).factorial * (a * b).factorial := by
      simp [Finset.prod_insert, show a - 1 ≠ a by omega, show a - 1 ≠ b - 1 by omega,
        show a - 1 ≠ b by omega, show a - 1 ≠ a * b - 1 by omega,
        show a - 1 ≠ a * b by omega, show a ≠ b - 1 by omega,
        show a ≠ b by omega, show a ≠ a * b - 1 by omega,
        show a ≠ a * b by omega, show b - 1 ≠ b by omega,
        show b - 1 ≠ a * b - 1 by omega, show b - 1 ≠ a * b by omega,
        show b ≠ a * b - 1 by omega, show b ≠ a * b by omega,
        show a * b - 1 ≠ a * b by omega, mul_assoc]
    rw [hprod]
    refine ⟨a * b * (a - 1).factorial * (b - 1).factorial * (a * b - 1).factorial, ?_⟩
    rw [← Nat.mul_factorial_pred (show a ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show b ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show a * b ≠ 0 by nlinarith)]
    ring
@[category API, AMS 11]
theorem product_adjacent_rep_four {a : ℕ} (ha : 2 ≤ a) : HasRepresentation (a * (a + 1)) 4 := by
  have hn0 : a + 3 ≤ a * (a + 1) := by nlinarith
  have h1 : 0 < a - 1 := by omega
  have h2 : a - 1 < a + 1 := by omega
  have h3 : a + 1 < a * (a + 1) - 1 := by omega
  have h4 : a * (a + 1) - 1 < a * (a + 1) := by omega
  refine ⟨{a - 1,a + 1,a * (a + 1) - 1,a * (a + 1)}, ?_, by simp, ?_, ?_⟩
  · simp [show a - 1 ≠ a + 1 by omega, show a - 1 ≠ a * (a + 1) - 1 by omega,
      show a - 1 ≠ a * (a + 1) by omega, show a + 1 ≠ a * (a + 1) - 1 by omega,
      show a + 1 ≠ a * (a + 1) by omega, show a * (a + 1) - 1 ≠ a * (a + 1) by omega]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · have hprod : (∏ x ∈ ({a - 1,a + 1,a * (a + 1) - 1,a * (a + 1)} : Finset ℕ), x.factorial) =
        (a - 1).factorial * (a + 1).factorial * (a * (a + 1) - 1).factorial * (a * (a + 1)).factorial := by
      simp [Finset.prod_insert, show a - 1 ≠ a + 1 by omega, show a - 1 ≠ a * (a + 1) - 1 by omega,
        show a - 1 ≠ a * (a + 1) by omega, show a + 1 ≠ a * (a + 1) - 1 by omega,
        show a + 1 ≠ a * (a + 1) by omega, show a * (a + 1) - 1 ≠ a * (a + 1) by omega, mul_assoc]
    rw [hprod]
    refine ⟨a * (a + 1) * (a - 1).factorial * (a * (a + 1) - 1).factorial, ?_⟩
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (show a ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show a * (a + 1) ≠ 0 by nlinarith)]
    ring

@[category API, AMS 11]
theorem product_equal_rep_two {a : ℕ} (ha : 2 ≤ a) : HasRepresentation (a * a) 2 := by
  simpa [pow_two] using (square_hasMinimum_two (by omega : 1 < a)).2.1

@[category API, AMS 11]
theorem product_has_rep_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ HasRepresentation (a * b) k := by
  have hordered : ∀ x y : ℕ, 2 ≤ x → x ≤ y → ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ HasRepresentation (x * y) k := by
    intro x y hx hxy
    by_cases heq : x = y
    · subst y
      exact ⟨2, by omega, by omega, product_equal_rep_two hx⟩
    by_cases hadj : y = x + 1
    · subst y
      exact ⟨4, by omega, by omega, product_adjacent_rep_four hx⟩
    exact ⟨6, by omega, by omega, product_separated_rep_six hx (by omega)⟩
  by_cases hab : a ≤ b
  · exact hordered a b ha hab
  · simpa [Nat.mul_comm] using hordered b a hb (by omega)

/-- Existence of a representation implies existence of its actual minimum. -/
@[category API, AMS 11]
theorem exists_minimum_le {m k : ℕ} (hk : 2 ≤ k) (hrep : HasRepresentation m k) :
    ∃ j, j ≤ k ∧ HasMinimum m j := by
  classical
  have hex : ∃ j, 2 ≤ j ∧ HasRepresentation m j := ⟨k, hk, hrep⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨hk, hrep⟩,
    (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hlt hrepj
  exact (Nat.find_min hex hlt) ⟨hj, hrepj⟩

/-- Every nontrivial product has an actual minimum between two and six. -/
@[category API, AMS 11]
theorem product_minimum_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, k ≤ 6 ∧ HasMinimum (a * b) k := by
  obtain ⟨j, hj, hj6, hrep⟩ := product_has_rep_le_six ha hb
  obtain ⟨k, hkj, hk⟩ := exists_minimum_le hj hrep
  exact ⟨k, le_trans hkj hj6, hk⟩

/-- There is a square product of six distinct factorials with maximum argument $527$. -/
@[category API, AMS 11]
theorem rep_527_six : HasRepresentation 527 6 := by
  simpa using (product_separated_rep_six (a := 17) (b := 31) (by norm_num) (by norm_num))

/-- Distinct positive indices bounded by m give at most m factorials. -/
@[category API, AMS 11]
theorem rep_card_le {m k : ℕ} (hrep : HasRepresentation m k) : k ≤ m := by
  obtain ⟨s, hk, _, hbound, _⟩ := hrep
  have hs : s ⊆ Finset.Icc 1 m := by
    intro a ha
    have := hbound a ha
    simp only [Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card hs
  simpa [hk] using hc

/-- Every composite endpoint at least two has a minimum no larger than six. -/
@[category API, AMS 11]
theorem composite_minimum_le_six {m : ℕ} (hm : 2 ≤ m) (hp : ¬ Nat.Prime m) :
    ∃ k, k ≤ 6 ∧ HasMinimum m k := by
  obtain ⟨a, b, ham, hbm, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hm).mp hp
  have ha : 2 ≤ a := by
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp at hab <;> omega
  have hb : 2 ≤ b := by
    by_contra h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> simp at hab <;> omega
  simpa [hab] using product_minimum_le_six ha hb

/-- $D_k=\emptyset$ for $k>6$. Studied by Erdős and Graham [ErGr76]. -/
@[category research solved, AMS 11]
theorem erdos_374.variants.D_empty_above_six {k : ℕ} (hk : 6 < k) : D k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro m hm
  change HasMinimum m k at hm
  have hmk := rep_card_le hm.2.1
  have hm2 : 2 ≤ m := by omega
  have hnp : ¬ Nat.Prime m := by
    intro hp
    exact erdos_374.variants.prime_no_rep hp hm.2.1
  obtain ⟨j, hj, hjD⟩ := composite_minimum_le_six hm2 hnp
  have := minimum_unique hm hjD
  omega

/-- Elementary upper bound valid for every cardinality class. -/
@[category API, AMS 11]
theorem countD_le (k n : ℕ) : countD k n ≤ n := by
  classical
  unfold countD
  have h := Finset.card_filter_le (s := Finset.Icc 1 n) (p := fun m => HasMinimum m k)
  simpa using h

/--
For any $m\in \mathbb{N}$, let $F(m)$ be the minimal $k\geq 2$ (if it exists) such
that there are $a_1<\cdots <a_k=m$ with $a_1!\cdots a_k!$ a square.
Let $D_k=\{ m : F(m)=k\}$. What is the order of growth of
$\lvert D_k\cap\{1,\ldots,n\}\rvert$ for $3\leq k\leq 6$?
-/
@[category research open, AMS 11]
theorem erdos_374.parts.i :
    let growth : ℕ → ℕ → ℝ := answer(sorry)
    ∀ k, 3 ≤ k → k ≤ 6 →
      (fun n => (countD k n : ℝ)) =Θ[Filter.atTop] growth k := by
  sorry

/-- Is it true that $\lvert D_6\cap \{1,\ldots,n\}\rvert \gg n$? -/
@[category research open, AMS 11]
theorem erdos_374.parts.ii : answer(sorry) ↔ PositiveLowerDensitySix := by
  sorry

end Erdos374

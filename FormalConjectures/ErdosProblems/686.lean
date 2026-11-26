/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 686

*References:*
- [erdosproblems.com/686](https://www.erdosproblems.com/686)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math.
  Acad. Sci. Hungar. (1979), 71-80.
-/

@[expose] public section

namespace Erdos686

/--
Can every integer $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, question, AMS 11]
theorem erdos_686 :
    ∀ N ≥ (2 : ℕ), ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can every square $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, question, AMS 11]
theorem erdos_686.variants.square :
    ∀ N ≥ (2 : ℕ),  (IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can $4$ be written as
$$4=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, question, AMS 11]
theorem erdos_686.variants.four :
    ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
The number $4$ cannot be written as
$$4=\frac{\prod_{1\leq i\leq 2}(m+i)}{\prod_{1\leq i\leq 2}(n+i)}$$
for $m≥n+2$!
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.four_two :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 2),
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 2, (m + i)) / (∏ i ∈ Finset.Icc 1 2, (n + i)) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
    Finset.prod_singleton]
  push Not
  intro n m hm
  rw [ne_eq, eq_div_iff (by positivity : (↑((n + 1) * (n + (1 + 1))) : ℚ) ≠ 0)]
  push_cast
  intro h
  have h' : 4 * ((n + 1) * (n + 2)) = (m + 1) * (m + 2) := by exact_mod_cast h
  by_cases hc : m < 2 * (n + 1) <;> nlinarith

/--
The number $4$ cannot be written as
$$4=\frac{\prod_{1\leq i\leq 3}(m+i)}{\prod_{1\leq i\leq 3}(n+i)}$$
for $m≥n+3$!

See [comment section on erdosproblems.com](https://www.erdosproblems.com/forum/thread/686#post-4599)
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.four_three :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 3),
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 3, (m + i)) / (∏ i ∈ Finset.Icc 1 3, (n + i)) := by
  sorry

/--
The number $4$ cannot be written as
$$4=\frac{\prod_{1\leq i\leq 4}(m+i)}{\prod_{1\leq i\leq 4}(n+i)}$$
for $m\geq n+4$!

Indeed, writing $X_x = (2x+5)^2 - 5$, we have $16 \cdot \prod_{1\leq i\leq 4}(x+i) = X_x^2 - 16$
and $X_x \geq 20$, so $4 \cdot P(n, 4) = P(m, 4)$ would give
$(2X_n - X_m)(2X_n + X_m) = 48$ with $2X_n + X_m \geq 60$, which is impossible.
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.four_four :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 4),
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 4, (m + i)) / (∏ i ∈ Finset.Icc 1 4, (n + i)) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 4),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 3),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
    Finset.prod_singleton]
  push Not
  intro n m hm
  rw [ne_eq, eq_div_iff
    (by positivity : (↑((n + 1) * (n + 2) * (n + 3) * (n + 4)) : ℚ) ≠ 0)]
  push_cast
  intro h
  have hZ : (4 : ℤ) * (((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) * ((n : ℤ) + 4))
      = ((m : ℤ) + 1) * ((m : ℤ) + 2) * ((m : ℤ) + 3) * ((m : ℤ) + 4) := by
    exact_mod_cast h
  obtain ⟨Xn, hXn⟩ : ∃ Xn : ℤ, Xn = (2 * (n : ℤ) + 5) ^ 2 - 5 := ⟨_, rfl⟩
  obtain ⟨Xm, hXm⟩ : ∃ Xm : ℤ, Xm = (2 * (m : ℤ) + 5) ^ 2 - 5 := ⟨_, rfl⟩
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by omega
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hXn20 : (20 : ℤ) ≤ Xn := by
    rw [hXn]
    nlinarith [mul_nonneg hn0 (show (0 : ℤ) ≤ 2 * (n : ℤ) + 10 by linarith)]
  have hXm20 : (20 : ℤ) ≤ Xm := by
    rw [hXm]
    nlinarith [mul_nonneg hm0 (show (0 : ℤ) ≤ 2 * (m : ℤ) + 10 by linarith)]
  have hfac : (2 * Xn - Xm) * (2 * Xn + Xm) = 48 := by
    rw [hXn, hXm]
    linear_combination 16 * hZ
  have hB : (60 : ℤ) ≤ 2 * Xn + Xm := by linarith
  rcases (by omega : (2 * Xn - Xm) ≤ 0 ∨ (0 : ℤ) < 2 * Xn - Xm) with hle | hlt
  · have hnonpos : (2 * Xn - Xm) * (2 * Xn + Xm) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
    linarith
  · have hge : (2 * Xn + Xm) ≤ (2 * Xn - Xm) * (2 * Xn + Xm) := by
      conv_lhs => rw [← one_mul (2 * Xn + Xm)]
      exact mul_le_mul_of_nonneg_right (by omega) (by linarith)
    linarith

/--
Can $9$ be written as
$$9=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research solved, question, AMS 11]
theorem erdos_686.variants.nine :
    ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (9 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  -- Witness: k = 3, n = 11, m = 25, since (26·27·28)/(12·13·14) = 19656/2184 = 9.
  refine ⟨3, by norm_num, 11, 25, by norm_num, ?_⟩
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/--
Can $25$ be written as
$$25=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, question, AMS 11]
theorem erdos_686.variants.twenty_five :
    ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
The number $25$ cannot be written as
$$25=\frac{\prod_{1\leq i\leq 2}(m+i)}{\prod_{1\leq i\leq 2}(n+i)}$$
for $m\geq n+2$!

Indeed, $r \cdot \prod_{1\leq i\leq 2}(x+i) = (\sqrt r (2x+3))^2 - r$ up to the factor $4$:
for $r = 25$ the equation $25 \cdot P(n, 2) = P(m, 2)$ becomes
$(5V - U)(5V + U) = 24$ with $U = 2m + 3$, $V = 2n + 3$. Since $5V + U \geq 22$ this forces
$5V - U = 1$, but $5V - U = 10n - 2m + 12$ is even, which is impossible.
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.twenty_five_two :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 2),
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 2, (m + i)) / (∏ i ∈ Finset.Icc 1 2, (n + i)) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
    Finset.prod_singleton]
  push Not
  intro n m hm
  rw [ne_eq, eq_div_iff (by positivity : (↑((n + 1) * (n + 2)) : ℚ) ≠ 0)]
  push_cast
  intro h
  have hZ : (25 : ℤ) * (((n : ℤ) + 1) * ((n : ℤ) + 2))
      = ((m : ℤ) + 1) * ((m : ℤ) + 2) := by exact_mod_cast h
  obtain ⟨U, hU⟩ : ∃ U : ℤ, U = 2 * (m : ℤ) + 3 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℤ, V = 2 * (n : ℤ) + 3 := ⟨_, rfl⟩
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by omega
  have hmZ : (n : ℤ) + 2 ≤ (m : ℤ) := by exact_mod_cast hm
  have hfac : (5 * V - U) * (5 * V + U) = 24 := by
    rw [hU, hV]
    linear_combination 4 * hZ
  have hB : (22 : ℤ) ≤ 5 * V + U := by linarith
  have ha_pos : (0 : ℤ) < 5 * V - U := by
    rcases (by omega : (5 * V - U) ≤ 0 ∨ (0 : ℤ) < 5 * V - U) with hle | hlt
    · have hnonpos : (5 * V - U) * (5 * V + U) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
      linarith
    · exact hlt
  have ha_le : 5 * V - U ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hge : (44 : ℤ) ≤ (5 * V - U) * (5 * V + U) :=
      mul_le_mul (by omega : (2 : ℤ) ≤ 5 * V - U) hB (by norm_num) (by linarith)
    linarith
  have ha_eq : 5 * V - U = 1 := by omega
  omega

/--
The number $25$ cannot be written as
$$25=\frac{\prod_{1\leq i\leq 4}(m+i)}{\prod_{1\leq i\leq 4}(n+i)}$$
for $m\geq n+4$!

Indeed, writing $X_x = (2x+5)^2 - 5$, we have $16 \cdot \prod_{1\leq i\leq 4}(x+i) = X_x^2 - 16$
and $X_x \geq 20$, so $25 \cdot P(n, 4) = P(m, 4)$ would give
$(5X_n - X_m)(5X_n + X_m) = 384$ with $5X_n + X_m \geq 120$, forcing $5X_n - X_m \in \{1, 2, 3\}$;
but then $10 X_n = (5X_n - X_m) + (5X_n + X_m)$ would equal $385$, $194$ or $131$,
none of which is divisible by $10$.
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.twenty_five_four :
    ¬ ∃ᵉ (n : ℕ) (m ≥ n + 4),
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 4, (m + i)) / (∏ i ∈ Finset.Icc 1 4, (n + i)) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 4),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 3),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
    Finset.prod_singleton]
  push Not
  intro n m hm
  rw [ne_eq, eq_div_iff
    (by positivity : (↑((n + 1) * (n + 2) * (n + 3) * (n + 4)) : ℚ) ≠ 0)]
  push_cast
  intro h
  have hZ : (25 : ℤ) * (((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) * ((n : ℤ) + 4))
      = ((m : ℤ) + 1) * ((m : ℤ) + 2) * ((m : ℤ) + 3) * ((m : ℤ) + 4) := by
    exact_mod_cast h
  obtain ⟨Xn, hXn⟩ : ∃ Xn : ℤ, Xn = (2 * (n : ℤ) + 5) ^ 2 - 5 := ⟨_, rfl⟩
  obtain ⟨Xm, hXm⟩ : ∃ Xm : ℤ, Xm = (2 * (m : ℤ) + 5) ^ 2 - 5 := ⟨_, rfl⟩
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by omega
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hXn20 : (20 : ℤ) ≤ Xn := by
    rw [hXn]
    nlinarith [mul_nonneg hn0 (show (0 : ℤ) ≤ 2 * (n : ℤ) + 10 by linarith)]
  have hXm20 : (20 : ℤ) ≤ Xm := by
    rw [hXm]
    nlinarith [mul_nonneg hm0 (show (0 : ℤ) ≤ 2 * (m : ℤ) + 10 by linarith)]
  have hfac : (5 * Xn - Xm) * (5 * Xn + Xm) = 384 := by
    rw [hXn, hXm]
    linear_combination 16 * hZ
  have hB : (120 : ℤ) ≤ 5 * Xn + Xm := by linarith
  have ha_pos : (0 : ℤ) < 5 * Xn - Xm := by
    rcases (by omega : (5 * Xn - Xm) ≤ 0 ∨ (0 : ℤ) < 5 * Xn - Xm) with hle | hlt
    · have hnonpos : (5 * Xn - Xm) * (5 * Xn + Xm) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
      linarith
    · exact hlt
  have ha_le : 5 * Xn - Xm ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have hge : (480 : ℤ) ≤ (5 * Xn - Xm) * (5 * Xn + Xm) :=
      mul_le_mul (by omega : (4 : ℤ) ≤ 5 * Xn - Xm) hB (by norm_num) (by linarith)
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = 5 * Xn - Xm := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℤ, B = 5 * Xn + Xm := ⟨_, rfl⟩
  have hfac' : a * B = 384 := by rw [ha, hBdef]; exact hfac
  have hB' : (120 : ℤ) ≤ B := by rw [hBdef]; exact hB
  have ha10 : 10 * Xn = a + B := by linarith
  have ha1 : (1 : ℤ) ≤ a := by omega
  have ha3 : a ≤ 3 := by omega
  interval_cases a <;> omega

/--
Can every non-square $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research solved, question, AMS 11]
theorem erdos_686.variants.non_square :
    ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  intro N hN_ge_2 hN_not_square

  have hN_not_square' : ¬ ∃ s, s * s = N := fun ⟨s, hs⟩ => hN_not_square ⟨s, hs.symm⟩

  -- 1. Setup the existence for k = 2 and simplify the products
  exists 2, by valid
  field_simp
  simp [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

  -- 2. Case split on the existence of solutions for small bounds
  by_cases h : {n | ∃ k, N * ((n + 1) * (n + 2)) = (k + 1) * (k + 2)}.Nonempty
  · obtain rfl | hN_lt := hN_ge_2.eq_or_lt
    · exact mod_cast
        if a : ∃ a ∈ Finset.range 30, ∃ n ∈ Finset.range 30, _ then
          a.imp fun a s => s.2.imp fun and => And.right
        else
          by exact (a (by native_decide)).elim

    obtain rfl | hN_ne_3 := eq_or_ne N 3
    · exact mod_cast
        if a : ∃ a ∈ Finset.range 30, ∃ n ∈ Finset.range 30, _ then
          a.imp fun and μ => μ.2.imp fun and => And.right
        else
          by exact (a (by native_decide)).elim

    exact h.mono fun and =>
      .imp fun a s =>
        mod_cast (by refine ⟨by
            nlinarith only [pow_three and, s, show N > 3 by valid], ?_⟩; push_cast [s.symm]; field_simp)

  -- 3. Reduce the general case to Pell's Equation
  convert (Pell.exists_of_not_isSquare _)
  show @@_ ↔ ¬ IsSquare (N * 4 : ℤ) → _
  · use
      mod_cast h.elim ∘ .imp (fun n ⟨m, hle, heq⟩ => ⟨m, by
        push_cast at heq; rw [eq_div_iff (by positivity : ((n : ℚ) + 1) * (↑n + 2) ≠ 0)] at heq
        exact_mod_cast heq⟩),
      (. (mod_cast hN_not_square' ∘ .rec (by
          use . / 2
          norm_num [←., true, Nat.div_mul_div_comm _, ((2).pow_dvd_pow_iff two_ne_zero).1, false, sq]))
        |>.elim ↑? _)

    use fun and ⟨A, B, _⟩ =>
      absurd
        (eq_add_of_sub_eq B)
        (A.natAbs_sq ▸ and.natAbs_sq ▸ mod_cast fun and => h ?_)

    -- Parity analysis
    obtain ⟨l, hl⟩ | ⟨a, ha⟩ := ((by · bound : ℤ)).natAbs.even_or_odd
    · exact absurd
        (and.trans (by rw [mul_right_comm]) |>.symm.trans (by rw [(by valid :), sq, add_mul]))
        (by valid)

    match a with
    | 0 => simp_all
    | S + 1 =>
        use A.natAbs + S, N * A.natAbs + S, by nlinarith only [‹_› ▸ and]

  omega

-- TODO: also formalize the follow-up question:
-- “If $n$ and $k$ are fixed then can one say anything about the set of integers so represented?”

end Erdos686

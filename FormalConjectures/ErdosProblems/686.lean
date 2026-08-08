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

import FormalConjecturesUtil

/-!
# Erdős Problem 686

*References:*
- [erdosproblems.com/686](https://www.erdosproblems.com/686)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math.
  Acad. Sci. Hungar. (1979), 71-80.
-/

namespace Erdos686

/--
Can every integer $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, AMS 11]
theorem erdos_686 :
    answer(sorry) ↔ ∀ N ≥ (2 : ℕ), ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can every square $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, AMS 11]
theorem erdos_686.variants.square :
    answer(sorry) ↔ ∀ N ≥ (2 : ℕ),  (IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can $4$ be written as
$$4=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, AMS 11]
theorem erdos_686.variants.four :
    answer(sorry) ↔ ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
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
  push_neg
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
Can $9$ be written as
$$9=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.nine :
    answer(True) ↔ ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (9 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  -- Witness: k = 3, n = 11, m = 25, since (26·27·28)/(12·13·14) = 19656/2184 = 9.
  simp only [true_iff]
  refine ⟨3, by norm_num, 11, 25, by norm_num, ?_⟩
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

/--
Can $25$ be written as
$$25=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research open, AMS 11]
theorem erdos_686.variants.twenty_five :
    answer(sorry) ↔ ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  sorry

/--
Can every non-square $N≥2$ be written as
$$N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$
for some $k≥2$ and $m≥n+k$?
-/
@[category research solved, AMS 11]
theorem erdos_686.variants.non_square :
    answer(True) ↔ ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  refine ⟨fun _ N hN_ge_2 hN_not_square => ?_, fun _ => trivial⟩

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

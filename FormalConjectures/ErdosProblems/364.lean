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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ForMathlib.NumberTheory.Powerful

/-!
# Erdős Problem 364

*Reference:* [erdosproblems.com/364](https://www.erdosproblems.com/364)
-/


/-- There is no consecutive triple of powerful numbers. -/
@[category research open, AMS 11]
theorem erdos_364 :
    ¬ ∃ (n : ℕ), powerful n ∧ powerful (n + 1) ∧ powerful (n + 2) := by
  sorry

/--
Erdős [Er76d] conjectured a stronger statement: if $n_k$ is the $k$th powerful number,
then $n_{k+2} - n_k > n_k^c$ for some constant $c > 0$.
-/
@[category research open, AMS 11]
theorem erdos_364_strong :
    ∃ (c : ℝ) (h : c > 0), ∀ (k : ℕ),
    Nat.nth powerful (k + 2) - Nat.nth powerful k > (Nat.nth powerful k : ℝ) ^ c := by
  sorry

/-- At least one of n, n + 1, n + 2, n + 3 is 2 mod 4. -/
@[category API, AMS 11]
lemma consecutive_2mod4 (n : ℕ) :
    (n % 4 = 2) ∨ ((n + 1) % 4 = 2) ∨ ((n + 2) % 4 = 2) ∨ ((n + 3) % 4 = 2) := by
  set r := n % 4
  set k := n / 4

  have hr : r < 4 := Nat.mod_lt n (by norm_num : 0 < 4)
  have hdiv : 4 * k + r = n := Nat.div_add_mod n 4

  interval_cases r
  · -- r = 0 ⇒ n = 4 * k ⇒ (n + 2) % 4 = 2
    right; right; left;
    simp at hdiv
    calc
      (n + 2) % 4 = (4 * k + 2) % 4 := by rw [hdiv]
      _ = 2 := by simp
  · -- r = 1 ⇒ n = 4 * k + 1 ⇒ (n + 1) % 4 = 2
    right; left;
    calc
      (n + 1) % 4 = (4 * k + 1 + 1) % 4 := by rw [hdiv]
      _ = (4 * k + (1 + 1)) % 4 := by ring
      _ = 2 := by norm_num
  · -- r = 2
    left;
    rfl
  · -- r = 3 ⇒ n = 4 * k + 3 ⇒ (n + 3) % 4 = 2
    right; right; right;
    calc
      (n + 3) % 4 = (4 * k + 3 + 3) % 4 := by rw [hdiv]
      _ = (4 * k + (3 + 3)) % 4 := by ring
      _ = 2 := by norm_num

/--
There is no quadruple of powerful numbers, since at least one of the four numbers must be
2 mod 4, which cannot be powerful (since 2 divides it, but 2^2 does not).
-/
@[category undergraduate, AMS 11]
theorem erdos_364_weak :
    ¬ ∃ (n : ℕ), powerful n ∧ powerful (n + 1) ∧ powerful (n + 2) ∧ powerful (n + 3) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h2mod4 := consecutive_2mod4 n
  cases h2mod4 with
  | inl h2 => exact (powerful_not_2mod4 n h2) hn.1
  | inr h2 =>
    cases h2 with
    | inl h2 => exact (powerful_not_2mod4 (n + 1) h2) hn.2.1
    | inr h2 =>
      cases h2 with
      | inl h2 => exact powerful_not_2mod4 (n + 2) h2 hn.2.2.1
      | inr h2 => exact powerful_not_2mod4 (n + 3) h2 hn.2.2.2

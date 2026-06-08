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

/-!
# Erdős Problem 1054

*Reference:* [erdosproblems.com/1054](https://www.erdosproblems.com/1054)
-/

namespace Erdos1054

open Classical Filter Asymptotics

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest
divisors of $m$ for some $k\geq 1$. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : ∃ᵉ (m) (k ≥ 1), n = ∑ i < k, Nat.nth (· ∈ m.divisors) i then
    Nat.find h
  else 0

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$?-/
@[category research open, AMS 11]
theorem erdos_1054.parts.i : answer(sorry) ↔ (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$ for almost all $n$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.ii : answer(sorry) ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $\limsup f(n)/n=\infty$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.iii : answer(sorry) ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    atTop.limsup (fun n ↦ (f n : EReal) / n) = ⊤ := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=2$, i.e. we get the junk value $0$. -/
@[category textbook, AMS 11]
theorem f_undefined_at_2 : f 2 = 0 := by
  rw [f, dif_neg]
  rintro ⟨m, k, hk, hsum⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp at hsum
  · -- For `m ≠ 0` the smallest divisor is `1` and every later term is `≥ 2`, so the sum of the
    -- `k` smallest divisors is `1` or `≥ 3`, never `2`.
    have hk0 : (0 : ℕ) ∈ Finset.Iio k := Finset.mem_Iio.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hk0, Nat.nth_divisors_zero hm] at hsum
    obtain ⟨i, hi_mem, hi_ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (s := (Finset.Iio k).erase 0)
        (f := Nat.nth (· ∈ m.divisors)) (by omega)
    have h2 := Nat.two_le_nth_divisors hm (Finset.ne_of_mem_erase hi_mem) hi_ne
    have := h2.trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi_mem)
    omega

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=5$, i.e. we get the junk value $0$. -/
@[category textbook, AMS 11]
theorem f_undefined_at_3 : f 5 = 0 := by
  sorry

end Erdos1054

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
# Riesel number

*References:*
- [Wikipedia, Riesel number](https://en.wikipedia.org/wiki/Riesel_number)
- [Ri56] Riesel, H., Några stora primtal. Elementa 39 (1956), 258–260.

A positive odd integer $k$ is a *Riesel number* if $k \cdot 2^n - 1$ is composite for all
natural numbers $n$. In 1956, Hans Riesel proved that there are infinitely many such numbers,
showing in particular that 509203 is a Riesel number. It is conjectured to be the smallest.

## Riesel problem

The *Riesel problem* asks: is 509203 the smallest Riesel number?

## Prime Riesel problem

The *prime Riesel problem* asks: is 509203 the smallest prime Riesel number?
-/

@[expose] public section

namespace RieselNumber

@[category test, AMS 11]
theorem not_isRieselNumber_one : ¬ Nat.IsRieselNumber 1 := by
  intro h
  have h3 : (1 * 2 ^ 2 - 1).Composite := h.2 2
  have : 1 * 2 ^ 2 - 1 = 3 := by rfl
  rw [this] at h3
  exact h3.2 (by norm_num)

@[category test, AMS 11]
theorem not_isRieselNumber_three : ¬ Nat.IsRieselNumber 3 := by
  intro h
  have h5 : (3 * 2 ^ 1 - 1).Composite := h.2 1
  have : 3 * 2 ^ 1 - 1 = 5 := by rfl
  rw [this] at h5
  exact h5.2 (by norm_num)

/--
Hans Riesel proved in 1956 that 509203 is a Riesel number by showing that all numbers of the form
$509203 \cdot 2^n - 1$ have a factor in the covering set $\{3, 5, 7, 13, 17, 241\}$.
-/
@[category research solved, AMS 11]
theorem riesel_509203 : Nat.IsRieselNumber 509203 := by
  sorry

/--
Hans Riesel proved in 1956 that there are infinitely many Riesel numbers.
-/
@[category research solved, AMS 11]
theorem infinitely_many_riesel_numbers :
    Set.Infinite {k : ℕ | k.IsRieselNumber} := by
  sorry

/--
**The Riesel problem.** Is 509203 the smallest Riesel number?

Hans Riesel conjectured that 509203 is the smallest Riesel number. He proved in 1956 that
509203 is indeed a Riesel number by showing that all numbers of the form $509203 \cdot 2^n - 1$
have a factor in the covering set $\{3, 5, 7, 13, 17, 241\}$.
-/
@[category research open, question, AMS 11]
theorem riesel_conjecture :
    IsLeast {k | k.IsRieselNumber} 509203 := by
  sorry

/--
**The prime Riesel problem.** Is 509203 the smallest prime Riesel number?
-/
@[category research open, question, AMS 11]
theorem prime_riesel_problem :
    IsLeast {k | k.IsRieselNumber ∧ k.Prime} 509203 := by
  sorry

end RieselNumber


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
# Infinitude of lucky primes and twin lucky numbers

Gardiner, Lazarus, Metropolis, and Ulam (1956) defined the *lucky numbers*
$1, 3, 7, 9, 13, 15, 21, 25, 31, \dots$ (OEIS A000959) via an iterative positional sieve on
positive integers: starting from the odd integers, step $s + 1$ removes every $m$-th surviving
entry, where $m$ is the $(s + 2)$-nd surviving term. Hawkins and Briggs (1957) proved the
asymptotic count $|\{k \le x : k \text{ lucky}\}| \sim x / \log x$. Whether infinitely many lucky
primes (OEIS A031157) or infinitely many twin lucky pairs $(n, n + 2)$ exist remains open
(Guy 2004, Section C3).

*References:*
- [Wikipedia: Lucky number](https://en.wikipedia.org/wiki/Lucky_number)
- [OEIS A000959](https://oeis.org/A000959)
- [OEIS A031157](https://oeis.org/A031157)
- V. Gardiner, R. Lazarus, N. Metropolis, and S. Ulam, *On certain sequences of integers defined by
  sieves*, Mathematics Magazine **29** (1956), no. 3, 117–122.
- D. Hawkins and W. E. Briggs, *The lucky number theorem*, Mathematics Magazine **31** (1957),
  81–84, 277–280.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer, 2004, Section C3.
-/

@[expose] public section

namespace LuckyNumber

/-- Verifies the first nine lucky numbers $1, 3, 7, 9, 13, 15, 21, 25, 31$ (including composite
sieve step $m = 9$ removing $27$). -/
@[category test, AMS 11]
theorem luckyNumber_first_nine :
    List.map luckyNumber [0, 1, 2, 3, 4, 5, 6, 7, 8] = [1, 3, 7, 9, 13, 15, 21, 25, 31] :=
  rfl

/-- Verifies that $7$ belongs to the lucky sequence. -/
@[category test, AMS 11]
theorem isLuckyNumber_seven : IsLuckyNumber 7 :=
  ⟨2, rfl⟩

/-- Verifies that $2$ does not belong to the lucky sequence. -/
@[category test, AMS 11]
theorem not_isLuckyNumber_two : ¬ IsLuckyNumber 2 := by
  rintro ⟨n, hn⟩
  have h := luckySieve_mod_two n n
  change luckyNumber n % 2 = 1 at h
  omega

/--
Infinitely many terms of the lucky sequence are prime (OEIS A031157).
-/
@[category research open, AMS 11]
theorem lucky_primes_infinitude :
    {p : ℕ | IsLuckyNumber p ∧ p.Prime}.Infinite := by
  sorry

/--
Infinitely many positive integers $n$ satisfy `IsLuckyNumber n` and `IsLuckyNumber (n + 2)`.
-/
@[category research open, AMS 11]
theorem twin_lucky_numbers_infinitude :
    {n : ℕ | IsLuckyNumber n ∧ IsLuckyNumber (n + 2)}.Infinite := by
  sorry

/--
Hawkins and Briggs (1957) proved that the count of lucky integers up to $x$ is asymptotic to
$x / \log x$ as $x \to \infty$.
-/
@[category research solved, AMS 11]
theorem hawkins_briggs_lucky_asymptotic :
    Filter.Tendsto
      (fun x : ℕ => (({k : ℕ | k ≤ x ∧ IsLuckyNumber k}.ncard : ℝ) * Real.log (x : ℝ)) / (x : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end LuckyNumber

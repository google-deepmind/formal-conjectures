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
$1, 3, 7, 9, 13, 15, 21, 25, 31, \dots$ (`A000959`) via an iterative positional sieve on positive
integers: starting from the odd integers, step $s + 1$ removes every $m$-th surviving entry, where
$m$ is the $(s + 2)$-nd surviving term. Hawkins and Briggs (1957) proved the asymptotic count
$|\{k \le x : k \text{ lucky}\}| \sim x / \log x$. Whether infinitely many lucky primes (`A031157`)
or infinitely many twin lucky pairs $(n, n + 2)$ exist remains open (Guy 2004, Section C3).

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

/-- Positional sieve generating Ulam's lucky sequence: `luckySieve 0 i = 2i + 1`, and stage `s + 1`
deletes every $m$-th surviving position where $m = \text{luckySieve } s\ (s + 1)$. -/
def luckySieve : ℕ → ℕ → ℕ
  | 0, i => 2 * i + 1
  | s + 1, i =>
    let m := luckySieve s (s + 1)
    luckySieve s (i + i / (m - 1))

/-- The $n$-th lucky number (0-indexed: $1, 3, 7, 9, 13, 15, 21, 25, 31, \dots$), using
stabilization of `luckySieve s n` once $s \ge n$. -/
def luckyNumber (n : ℕ) : ℕ :=
  luckySieve n n

/-- Membership predicate for Ulam's lucky sequence (`A000959`). -/
def IsLuckyNumber (k : ℕ) : Prop :=
  ∃ n : ℕ, luckyNumber n = k

/-- Verifies the first nine lucky numbers $1, 3, 7, 9, 13, 15, 21, 25, 31$ (including composite
sieve step $m = 9$ removing $27$). -/
@[category test, AMS 11]
theorem luckyNumber_first_nine :
    List.map luckyNumber [0, 1, 2, 3, 4, 5, 6, 7, 8] = [1, 3, 7, 9, 13, 15, 21, 25, 31] :=
  rfl

/-- Verifies that $7$ belongs to the lucky sequence whereas $2$ does not. -/
@[category test, AMS 11]
theorem isLuckyNumber_seven_and_not_two :
    IsLuckyNumber 7 ∧ ¬ IsLuckyNumber 2 := by
  refine ⟨⟨2, rfl⟩, ?_⟩
  have hodd : ∀ s i : ℕ, luckySieve s i % 2 = 1 := by
    intro s
    induction s with
    | zero => intro i; dsimp [luckySieve]; omega
    | succ s ih => intro i; exact ih _
  rintro ⟨n, hn⟩
  have h := hodd n n
  change luckyNumber n % 2 = 1 at h
  omega

/-- Once the sieve stage $s$ reaches at least $n$, `luckySieve s n` stabilizes at
`luckyNumber n`. -/
@[category API, AMS 11]
theorem luckySieve_stabilizes {n s : ℕ} (hns : n ≤ s) :
    luckySieve s n = luckyNumber n := by
  have hge : ∀ t i : ℕ, 2 * i + 1 ≤ luckySieve t i := fun t => by
    induction t with
    | zero => intro i; dsimp [luckySieve]; omega
    | succ t ih =>
      intro i; dsimp [luckySieve]
      have h1 := ih (i + i / (luckySieve t (t + 1) - 1))
      have h2 := Nat.le_add_right i (i / (luckySieve t (t + 1) - 1)); omega
  induction s with
  | zero => obtain rfl : n = 0 := (by omega); rfl
  | succ s ih =>
    by_cases hle : n ≤ s
    · dsimp [luckySieve]; have := hge s (s + 1)
      rw [Nat.div_eq_of_lt (by omega), add_zero, ih hle]
    · obtain rfl : n = s + 1 := (by omega); rfl

/--
Infinitely many terms of the lucky sequence are prime (`A031157`).
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

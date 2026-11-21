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
# The Sisyphus sequence

The Sisyphus sequence starts at $a(1)=1$. An even current value is halved. An odd current
value is increased by the next prime, using prime addends in increasing order. Terms may repeat.
We extend the official one-based sequence by $a(0)=0$.

*References:*
- [A350877](https://oeis.org/A350877)
-/

@[expose] public section

namespace OeisA350877

/-- A finite interval containing the least prime greater than $n$. -/
def primeCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 3)).filter fun p => n < p ∧ p.Prime

/-- Bertrand's postulate supplies a prime in the search interval. -/
@[category API, AMS 11]
theorem prime_candidates_nonempty (n : ℕ) : (primeCandidates n).Nonempty := by
  obtain ⟨p, hp, hnp, hbound⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n + 1) (by omega)
  refine ⟨p, ?_⟩
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by omega, hp⟩

/-- The least prime strictly greater than $n$, computed by a finite search. -/
def nextPrime (n : ℕ) : ℕ :=
  (primeCandidates n).min' (prime_candidates_nonempty n)

/-- The finite search returns a prime strictly greater than its input. -/
@[category API, AMS 11]
theorem next_prime_spec (n : ℕ) : n < nextPrime n ∧ (nextPrime n).Prime := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (primeCandidates n) (prime_candidates_nonempty n))).2

/-- No prime greater than $n$ is smaller than the returned prime. -/
@[category API, AMS 11]
theorem next_prime_le {n p : ℕ} (hnp : n < p) (hp : p.Prime) : nextPrime n ≤ p := by
  by_cases hbound : p < 2 * n + 3
  · apply Finset.min'_le
    simp only [primeCandidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨hbound, hnp, hp⟩
  · have hmem := Finset.min'_mem (primeCandidates n) (prime_candidates_nonempty n)
    have hsmall : nextPrime n < 2 * n + 3 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
    omega

/-- The current value and the most recent prime used as an addend. -/
structure State where
  current : ℕ
  lastPrime : ℕ
  deriving DecidableEq

/-- Halve an even value; otherwise add the next prime and record that addend. -/
def step (s : State) : State :=
  if s.current % 2 = 0 then
    ⟨s.current / 2, s.lastPrime⟩
  else
    let p := nextPrime s.lastPrime
    ⟨s.current + p, p⟩

/-- The state after $n$ transitions. The initial last addend is set to one. -/
def state : ℕ → State
  | 0 => ⟨1, 1⟩
  | n + 1 => step (state n)

/-- The Sisyphus sequence, with its official one-based indexing and the extension $a(0)=0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (state n).current

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 8 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 4 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide

@[category test, AMS 11]
theorem a_8 : a 8 = 1 := by decide

@[category test, AMS 11]
theorem a_9 : a 9 = 8 := by decide

@[category test, AMS 11]
theorem a_13 : a 13 = 12 := by decide

/-- The total extension at zero is separate from the official sequence. -/
@[category test, AMS 11]
theorem a_zero_extension : a 0 = 0 := by rfl

/-- An even transition leaves the last prime addend unchanged. -/
@[category API, AMS 11]
theorem step_even (s : State) (h : s.current % 2 = 0) :
    step s = ⟨s.current / 2, s.lastPrime⟩ := by
  simp [step, h]

/-- An odd transition consumes exactly the next prime addend. -/
@[category API, AMS 11]
theorem step_odd (s : State) (h : s.current % 2 ≠ 0) :
    step s = ⟨s.current + nextPrime s.lastPrime, nextPrime s.lastPrime⟩ := by
  simp [step, h]

/-- Every state reached from the initial value has a positive current value. -/
@[category API, AMS 11]
theorem state_current_pos (n : ℕ) : 0 < (state n).current := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [state, step]
      split <;> simp only
      · omega
      · omega

/-- The official sequence never contains zero. -/
@[category API, AMS 11]
theorem a_pos {n : ℕ} (hn : 0 < n) : 0 < a n := by
  cases n with
  | zero => omega
  | succ n => exact state_current_pos n

/-- Repeated values use different prime addends at different times. -/
@[category test, AMS 11]
theorem repeated_one_uses_next_prime :
    a 1 = a 8 ∧ a 2 ≠ a 9 := by
  decide

/-- "Will every positive integer appear in S?" — [A350877](https://oeis.org/A350877). -/
@[category research open, question, AMS 11]
theorem every_positive_integer_occurs :
    ∀ m : ℕ, 0 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OeisA350877

/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/219
import FormalConjectures.Util.ProblemImports

/--
The set of arithmetic progressions of primes
-/
def primeArithmeticProgressions : Set (List ℕ) :=
  {l | l ≠ [] ∧ (∀ p ∈ l, p.Prime) ∧ ∃ step ≠ 0, l.Chain' fun a b => b = step + a}

example : [3, 5, 7] ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions]
  norm_num

example : ¬[1, 2] ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions]
  norm_num

example : [] ∉ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions]

example {p : ℕ} (hp : p.Prime) : [p] ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions, hp]

example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) : [p, q] ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions, hp, hq]
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hpq
  exact ⟨n, by omega⟩

/--
Are there arbitrarily long arithmetic progressions of primes?
Solution: yes.
Ref: Green, Ben and Tao, Terence, _The primes contain arbitrarily long arithmetic progressions_
-/
@[problem_status solved]
theorem erdos_219 : ∀ N, ∃ l ∈ primeArithmeticProgressions, N ≤ l.length := by
  sorry

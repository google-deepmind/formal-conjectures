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
# Erdős Problem 219

*Reference:* [erdosproblems.com/219](https://www.erdosproblems.com/219)
-/

namespace Erdos219

/--
The set of arithmetic progressions of primes
-/
def primeArithmeticProgressions : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > 0, s.IsAPOfLength l}

@[category test, AMS 5 11]
theorem primeArithmeticProgression_3_5_7 : {3, 5, 7} ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions, Set.IsAPOfLength, Set.IsAPOfLengthWith]
  refine ⟨by norm_num, ⟨3, 2, Set.ext fun x => ?_⟩⟩
  refine ⟨fun h => ?_, fun ⟨w, ⟨hl, hr⟩⟩ => by interval_cases w <;> simp_all⟩
  cases h with
  | inl hl => simp [hl]
  | inr hr => cases hr with
    | inl hrl => simpa [hrl] using ⟨1, by simp⟩
    | inr hrr => simpa [hrr] using ⟨2, by aesop⟩

@[category test, AMS 5 11]
theorem not_primeArithmeticProgression_1_2 : ¬{1, 2} ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions]
  norm_num

@[category API, AMS 5 11]
theorem empty_not_primeArithmeticProgression : ∅ ∉ primeArithmeticProgressions := by
  simpa [primeArithmeticProgressions] using fun _ hl ↦ Set.not_isAPOfLength_empty hl

@[category API, AMS 5 11]
lemma singleton_mem_primeArithmeticProgressions
    {p : ℕ} (hp : p.Prime) : {p} ∈ primeArithmeticProgressions := by
  simpa [primeArithmeticProgressions, hp] using ⟨1, one_pos, by simp⟩

@[category API, AMS 5 11]
lemma pair_mem_primeArithmeticProgressions
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    {p, q} ∈ primeArithmeticProgressions := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hpq
  simpa [primeArithmeticProgressions, hp, hq] using ⟨2, by norm_num, Nat.isAPOfLength_pair hpq⟩

/--
Are there arbitrarily long arithmetic progressions of primes?
Solution: yes.
Ref: Green, Ben and Tao, Terence, _The primes contain arbitrarily long arithmetic progressions_
-/

@[category research solved, AMS 5 11]
theorem erdos_219 : (∀ N, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l) ↔ answer(True) := by
  sorry

end Erdos219

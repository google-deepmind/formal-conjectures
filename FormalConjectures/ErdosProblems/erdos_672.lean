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

-- Erdos Problems URL: https://www.erdosproblems.com/672
import FormalConjectures.Util.ProblemImports

/-- Erdos problem 672 conjectures the below holds for all `k ≥ 4` and `l > 1`. -/
def Erdos672With (k l : ℕ) [NeZero k] : Prop :=
  ∀ᵉ (s : Fin k → ℕ), 0 < s 0 → (∃ d > 0, ∀ i, s i = s 0 + i * d) → ¬ ∃ q, ∏ i, s i = q ^ l

/-- Can the product of an arithmetic progression of positive integers of length ≥ 4 be a perfect power? -/
@[problem_status open]
theorem erdos_672
    (k l : ℕ) (hk : 4 ≤ k) (hl : 1 < l)
    (hk' : NeZero k := ⟨Nat.not_eq_zero_of_lt hk⟩) :
    Erdos672With k l :=
  sorry

/-- According to https://www.erdosproblems.com/672, Euler proved this. -/
lemma erdos_672.variants.euler :
    Erdos672With 4 2 :=
  sorry

/-- According to https://www.erdosproblems.com/672, Obláth proved this.

[Ob51] Oblath, Richard, Eine Bemerkung über Produkte aufeinander folgender Zahlen.
J. Indian Math. Soc. (N.S.) (1951), 135-139. -/
lemma erdos_672.variants.oblath :
    Erdos672With 5 2 ∧ Erdos672With 3 3 ∧ Erdos672With 3 4 ∧ Erdos672With 3 5 :=
  sorry

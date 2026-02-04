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
import FormalConjecturesForMathlib.Data.Set.Density

open Filter Finset Real Classical
open Set

/--
Erdős Problem 696: Sequence Chains in Divisors
See: https://www.erdosproblems.com/696
-/

namespace Erdos696

/-
This problem is about how long a chain of divisors can be if each element
has to be 1 modulo the previous one. We define two variations:
h(n) for prime divisors and H(n) for any divisors.
-/

variable (n : ℕ)

def ValidChain (P : ℕ → Prop) (s : List ℕ) : Prop :=
  s.Chain' (fun a b => a < b ∧ b % a = 1) ∧ ∀ d ∈ s, d ∣ n ∧ P d

/-- Largest number of prime divisors in a chain. -/
noncomputable def h : ℕ :=
  Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n Nat.Prime s) n

/-- Largest number of any divisors in a chain. -/
noncomputable def H : ℕ :=
  Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n (fun _ => True) s) n

/-- The iterated logarithm: how many times we take log to get below e. -/
noncomputable def L (x : ℝ) : ℝ := sorry

/-- Erdős conjectured h(n) is typically log*(n). -/
@[category research open, AMS 11]
theorem typical_h : ∀ ε > 0, {n : ℕ | abs ((h n : ℝ) / L (n : ℝ) - 1) < (ε : ℝ)}.HasDensity 1 := by
  sorry

/-- Does H(n) tend to be much larger than h(n)? -/
@[category research open, AMS 11]
theorem ratio_limit : answer(sorry) ↔ ∀ M : ℝ, {n : ℕ | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) > M}.HasDensity 1 := by
  sorry

/-- Estimation of the individual growth rates. -/
@[category research open, AMS 11]
theorem growth_h : answer(sorry) ↔ ∃ f : ℕ → ℝ, ∀ ε > 0, {n : ℕ | abs ((h n : ℝ) / f n - 1) < (ε : ℝ)}.HasDensity 1 := by
  sorry

@[category research open, AMS 11]
theorem growth_H : answer(sorry) ↔ ∃ f : ℕ → ℝ, ∀ ε > 0, {n : ℕ | abs ((H n : ℝ) / f n - 1) < (ε : ℝ)}.HasDensity 1 := by
  sorry

end Erdos696

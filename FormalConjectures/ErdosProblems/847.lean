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
# Erdős Problem 847

*Reference:* [erdosproblems.com/847](https://www.erdosproblems.com/847)
-/

open Nat

namespace Erdos847

#check List.range'
#check List.range
#check List.toSSet
#check Infinite

-- there is a subset of S with a three term arithmetic progression
def containsThreeTermArithProg (S : Set ℕ) : Prop :=
    ∃ a b c, {a, b, c} ⊆ S ∧ ∃ t, [a, b, c] = List.range' a 3 t

def hε (A : Set ℕ) :=
  ∃ (ε : ℝ), ∀ (B : Set ℕ), B ⊆ A →
  ∃ (C : Set ℕ), C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ¬ containsThreeTermArithProg C


/--
Let A⊂N be an infinite set for which there exists some ϵ > 0 such that in any subset of A of size n
there is a subset of size at least ϵ n which contains no three-term arithmetic progression.

Is it true that A is the union of a finite number of sets which contain no three-term arithmetic progression?
-/
@[category research open, AMS 11]
theorem erdos_847
    (A : Set ℕ) (hinf : Infinite A) (heps : hε A) :
  answer(sorry) ↔
  ∃ n, ∃ (S : Fin n → Set ℕ), (∀ i, ¬ containsThreeTermArithProg (S i)) ∧ A = ⋃ i : Fin n, S i :=
  sorry

end Erdos847

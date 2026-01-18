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
import Mathlib.Data.Nat.Basic

namespace Nat

/--
A [perfect power](https://en.wikipedia.org/wiki/Perfect_power) is a natural number that
  is a product of equal natural factors, or, in other words, an integer that can be expressed
  as a square or a higher integer power of another integer greater than one. More formally,
  $n$ is a perfect power if there exist natural numbers $m > 1$, and $k > 1$ such that
  $m ^ k = n$. In this case, $n$ may be called a perfect $k$th power. If $k = 2$ or
  $k = 3$, then $n$ is called a perfect square or perfect cube, respectively.
-/
def IsPerfectPower (n : ℕ) : Prop :=
    ∃ k m : ℕ, 1 < k ∧ 1 < m ∧ k ^ m = n

theorem IsPerfectPower.four : IsPerfectPower 4 :=
  ⟨2, 2, by decide, by decide, rfl⟩

theorem IsPerfectPower.twenty_seven : IsPerfectPower 27 :=
  ⟨3, 3, by decide, by decide, rfl⟩

end Nat

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
# Sum of two squares, a power of 3, and a power of 5

Any integer $n > 1$ can be written as $a^2 + b^2 + 3^c + 5^d$ where $a, b, c, d$ are
nonnegative integers.

Zhi-Wei Sun has offered a $3,500 prize for the first proof.

*Reference:* [A303656](https://oeis.org/A303656)
-/

namespace OeisA303656

/-- The predicate that `n` can be written as $a^2 + b^2 + 3^c + 5^d$ for nonnegative integers. -/
def IsSumOfTwoSquaresAndPowersOf3And5 (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + 3 ^ c + 5 ^ d

@[category test, AMS 11]
theorem isSumOfTwoSquaresAndPowersOf3And5_2 : IsSumOfTwoSquaresAndPowersOf3And5 2 :=
  ⟨0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfTwoSquaresAndPowersOf3And5_5 : IsSumOfTwoSquaresAndPowersOf3And5 5 :=
  ⟨0, 1, 1, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfTwoSquaresAndPowersOf3And5_25 : IsSumOfTwoSquaresAndPowersOf3And5 25 :=
  ⟨1, 4, 1, 1, by norm_num⟩

/--
**Zhi-Wei Sun's Conjecture (A303656)**: Any integer $n > 1$ can be written as the sum of two
squares, a power of 3, and a power of 5.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : IsSumOfTwoSquaresAndPowersOf3And5 n := by
  sorry

end OeisA303656

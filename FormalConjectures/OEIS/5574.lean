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
# Numbers $k$ such that $k^2 + 1$ is prime

References:

[A005574](https://oeis.org/A005574)
[edoc.unibas.ch/58842](https://edoc.unibas.ch/entities/publication/b5fc8a55-2b29-4f16-bf5a-343f0bf2b82c)
[MathOverflow](https://mathoverflow.net/questions/14690/primes-of-the-form-a21)

"This is from the Euler-Goldbach correspondence available online at [edoc.unibas.ch/58842]. The letter in question is dated Oct 1, 1742."
- Franz Lemmermeyer, comment on MathOverflow, Feb 6 2019, [MathOverflow]
-/

@[expose] public section

namespace OeisA5574

/-- The set of numbers $k$ such that $k ^ 2 + 1$ is prime. -/
def squareSuccIsPrime : Set ℕ := {k : ℕ | (k ^ 2 + 1).Prime}

@[category test, AMS 11]
theorem a_0 : 1 ∈ squareSuccIsPrime := by norm_num [squareSuccIsPrime]

@[category test, AMS 11]
theorem a_1 : 2 ∈ squareSuccIsPrime := by norm_num [squareSuccIsPrime]

@[category test, AMS 11]
theorem a_2 : 4 ∈ squareSuccIsPrime := by norm_num [squareSuccIsPrime]

@[category test, AMS 11]
theorem a_3 : 6 ∈ squareSuccIsPrime := by norm_num [squareSuccIsPrime]

@[category test, AMS 11]
theorem a_4 : 10 ∈ squareSuccIsPrime := by norm_num [squareSuccIsPrime]

/--
Apparently Goldbach conjectured that any $a > 1$ from this sequence can be written as $a = b + c$ where $b$ and $c$ are in this sequence ...
- Jeppe Stig Nielsen, Oct 14 2015, [A005574]

See also [edoc.unibas.ch/58842], [MathOverflow]
-/
@[category research open, AMS 11]
theorem conjecture : ∀ a ∈ squareSuccIsPrime, 1 < a → ∃ b c : squareSuccIsPrime, a = b + c := by
  sorry

end OeisA5574

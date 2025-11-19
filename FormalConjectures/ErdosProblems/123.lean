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
# Erdős Problem 123

*References:*
- [erdosproblems.com/123](https://www.erdosproblems.com/123)
- [ErLe96] Erdős, P. and Lewin, Mordechai, _$d$-complete sequences of integers_. Math. Comp. (1996), 837-840.
- [Er92b] Erdős, Paul, _Some of my favourite problems in various branches of combinatorics_. Matematiche (Catania) (1992), 231-240.
-/

namespace Erdos123

/--
Given three natural numbers `a`, `b`, `c`, this is the set of all natural numbers
of the form $a^k b^l c^m$ where $k, l, m ≥ 0$.
-/
def powersOfThree (a b c : ℕ) : Set ℕ :=
  {n | ∃ k l m : ℕ, n = a^k * b^l * c^m}

/--
Helper predicate for pairwise coprimality of three integers.
-/
def PairwiseCoprime (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

/--
**Erdős Problem #123**

Let a,b,c be three integers which are pairwise coprime. Is every large integer the sum of distinct integers of the form akblcm (k,l,m≥0), none of which divide any other?

ANSWER
-/
theorem erdos_123

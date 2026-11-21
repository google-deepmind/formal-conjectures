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
# Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists

For $n \ge 0$, $a(n)$ is the smallest positive integer $x$ such that $x \bmod \phi(x) = n$, or $0$
if no such $x$ exists, where $\phi$ is Euler's totient function.

*References:*
- [A234642](https://oeis.org/A234642)
-/

@[expose] public section

namespace OeisA234642

/--
The predicate that $x > 0$ satisfies $x \bmod \phi(x) = n$.
-/
def ModTotientEq (n x : ℕ) : Prop :=
  0 < x.totient ∧ x % x.totient = n

instance (n x : ℕ) : Decidable (ModTotientEq n x) :=
  inferInstanceAs (Decidable (0 < x.totient ∧ x % x.totient = n))

/--
Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | ModTotientEq n x}

@[category test, AMS 11]
theorem a_0 : a 0 = 1 :=
  IsLeast.csInf_eq (by decide)

@[category test, AMS 11]
theorem a_1 : a 1 = 3 :=
  IsLeast.csInf_eq (by decide)

@[category test, AMS 11]
theorem a_2 : a 2 = 10 :=
  IsLeast.csInf_eq (by decide)

@[category test, AMS 11]
theorem a_3 : a 3 = 9 :=
  IsLeast.csInf_eq (by decide)

@[category test, AMS 11]
theorem a_4 : a 4 = 20 :=
  IsLeast.csInf_eq (by decide)

/--
Conjecture: $a(n) > 0$ for all $n$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : 0 < a n := by
  sorry

end OeisA234642

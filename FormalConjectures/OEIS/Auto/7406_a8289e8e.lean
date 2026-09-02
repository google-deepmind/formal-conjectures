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

import FormalConjectures.Util.ProblemImports

open Finset Rat Int Nat

/--
A007406: Wolstenholme numbers: numerator of $\sum_{k=1}^n \frac{1}{k^2}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun k : ℕ => (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

/--
A089026: $a(n) = n$ if $n$ is prime, else $1$.
-/
def a089026 (n : ℕ) : ℕ :=
  if n.Prime then n else 1

/--
%C A007406 Conjecture: for n > 3, gcd(n, a(n-1)) = A089026(n).
-/
theorem a007406_conjecture_0 (n : ℕ) (hn : n > 3) :
    Nat.gcd n (a (n - 1)) = a089026 n :=
  by sorry
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

import FormalConjecturesUtil

/-!
# Erdős Problem 468

*Reference:* [erdosproblems.com/468](https://www.erdosproblems.com/468)
-/

namespace Erdos468

open Filter Asymptotics

/--
The partial sum of those divisors $d$ of $n$ satisfying $1<d\leq x$. When $x$ runs over the
divisors of $n$ greater than $1$, these are precisely the sums
$d_1,d_1+d_2,d_1+d_2+d_3,\ldots$ in increasing divisor order.
-/
def divisorPrefixSum (n x : ℕ) : ℕ := by
  classical
  exact ((Nat.divisors n).filter fun d => 1 < d ∧ d ≤ x).sum fun d => d

/-- The set $D_n$ from Erdős problem 468. -/
def D (n : ℕ) : Finset ℕ := by
  classical
  exact ((Nat.divisors n).filter fun d => 1 < d).image fun d => divisorPrefixSum n d

/-- The elements of $D_n$ which do not occur in any earlier $D_m$. -/
def newDivisorPrefixSums (n : ℕ) : Finset ℕ := by
  classical
  exact (D n).filter fun x => ∀ m : ℕ, m < n → x ∉ D m

/-- The natural number $n$ is the least index such that $N\in D_n$. -/
def IsMinimalDPreimage (N n : ℕ) : Prop :=
  N ∈ D n ∧ ∀ m : ℕ, N ∈ D m → n ≤ m

/-- The minimal preimage function exists on every representable value and is $o(N)$. -/
def Erdos468MinimalPreimageLittleO : Prop :=
  ∃ f : ℕ → ℕ,
    (∀ N : ℕ, (∃ n, N ∈ D n) → IsMinimalDPreimage N (f N)) ∧
      (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/--
The weaker "almost all" version: there is a function which is the minimal preimage function on a
set of natural density one and is still $o(N)$.
-/
def Erdos468MinimalPreimageLittleOAlmostAll : Prop :=
  ∃ f : ℕ → ℕ,
    {N : ℕ | IsMinimalDPreimage N (f N)}.HasDensity 1 ∧
      (fun N : ℕ => (f N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))

/-- What is the size of $D_n\setminus\bigcup_{m<n}D_m$? -/
@[category research open, AMS 11]
theorem erdos_468.parts.i :
    (fun n : ℕ => (newDivisorPrefixSums n).card) = answer(sorry) := by
  sorry

/--
If $f(N)$ is the minimal $n$ such that $N\in D_n$, is it true that $f(N)=o(N)$?
-/
@[category research open, AMS 11]
theorem erdos_468.parts.ii : answer(sorry) ↔ Erdos468MinimalPreimageLittleO := by
  sorry

/-- The "perhaps just for almost all $N$" variant from the problem page. -/
@[category research open, AMS 11]
theorem erdos_468.variants.almost_all :
    answer(sorry) ↔ Erdos468MinimalPreimageLittleOAlmostAll := by
  sorry

end Erdos468

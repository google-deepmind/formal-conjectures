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
# Erdős Problem 468

*References:*
- [erdosproblems.com/468](https://www.erdosproblems.com/468)
- [Ko26] Kovač, V., *An improved bound in Erdős problem #1054* (2026).
  https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_1054.pdf
- [Ku] Kumchev, A., *On the Piatetski-Shapiro–Vinogradov theorem*.
  https://tigerweb.towson.edu/akumchev/a3.pdf
-/

@[expose] public section

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

def erdos_468.parts.i.answer : ℕ → ℕ := sorry

/-- What is the size of $D_n\setminus\bigcup_{m<n}D_m$? -/
@[category research open, question value, AMS 11]
theorem erdos_468.parts.i :
    (fun n : ℕ => (newDivisorPrefixSums n).card) = erdos_468.parts.i.answer := by
  sorry

/--
If $f(N)$ is the minimal $n$ such that $N\in D_n$, is it true that $f(N)=o(N)$?
Here the minimal-preimage condition is restricted to representable values of $N$.

The answer is no. Kovač's counting bound [Ko26, Lemma 2 and the proof of Theorem 1] gives
upper density $O(\delta^4)$ for represented values with minimal preimage at most $\delta N$.
Including the divisor $1$ shifts each prefix sum by one, so the bound applies here.
Vinogradov's counting theorem [Ku, equation (1)] implies that all sufficiently large odd
$N$ are representable: they are sums of three distinct primes greater than $\sqrt{N}$.
Thus the represented values have positive lower density, which rules out $f(N)=o(N)$.
-/
@[category research solved, question, AMS 11]
theorem erdos_468.parts.ii : ¬ Erdos468MinimalPreimageLittleO := by
  sorry

/--
Perhaps just for almost all $N$?

The answer is no by Kovač's counting bound [Ko26, Lemma 2 and the proof of Theorem 1].
After shifting prefix sums by one to account for the omitted divisor $1$, this bound rules
out a set of density one on which the minimal preimage is $o(N)$.
-/
@[category research solved, question, AMS 11]
theorem erdos_468.variants.almost_all :
    ¬ Erdos468MinimalPreimageLittleOAlmostAll := by
  sorry

end Erdos468

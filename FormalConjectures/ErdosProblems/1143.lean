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

/-!
# Erdős Problem 1143

Estimate $F_k(p_1, \ldots, p_u)$, the minimum count of multiples of at least one given prime
in any interval of $k$ consecutive integers, particularly for $k = \alpha \cdot p_u$
with $\alpha > 2$.

*Reference:* [erdosproblems.com/1143](https://www.erdosproblems.com/1143)

[Va99] Vaughan, R.C., *On a problem of Erdős, Straus, and Schinzel*, Combinatorica 19 (1999),
111–115.
-/

open Finset

namespace Erdos1143

/-- Count of integers in $\{n+1, \ldots, n+k\}$ divisible by at least one element of $S$. -/
def countDivisible (S : Finset ℕ) (k n : ℕ) : ℕ :=
  ((Icc (n + 1) (n + k)).filter (fun m =>
    (S.filter (· ∣ m)).Nonempty)).card

/--
Erdős Problem 1143 [Va99, §1.8]:

Let $p_1 < \cdots < p_u$ be primes and $k \geq 1$. Define $F_k(p_1, \ldots, p_u)$ to be the
minimum, over all starting points $n \geq 0$, of the count of integers in
$\{n+1, \ldots, n+k\}$ that are divisible by at least one $p_i$.

Estimate $F_k(p_1, \ldots, p_u)$, particularly in the range $k = \alpha \cdot p_u$
for constant $\alpha > 2$.

Erdős and Selfridge found the exact bound when $2 < \alpha < 3$.
For $\alpha > 3$, very little is known.

We formalize a sieve lower bound: for any finite set of primes $S$,
every interval of $k$ consecutive positive integers contains at least
$$k \cdot \left(1 - \prod_{p \in S}\left(1 - \frac{1}{p}\right)\right) - 2^{|S|}$$
multiples of some element of $S$.
The open problem is to determine sharper estimates, particularly
the exact value of $F_k$ for $\alpha > 3$.
-/
@[category research open, AMS 11]
theorem erdos_1143 (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) (k : ℕ) (hk : 0 < k) :
    ∀ n : ℕ,
      (countDivisible S k n : ℝ) ≥
        (k : ℝ) * (1 - S.prod (fun p => (1 - 1 / (p : ℝ)))) - (2 : ℝ) ^ S.card := by
  sorry

end Erdos1143

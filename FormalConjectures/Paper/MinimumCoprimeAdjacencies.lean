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
# The Minimum Number of Coprime Adjacencies in a Permutation

*Reference:* G. Sidoine, *The Minimum Number of Coprime Adjacencies in a
Permutation*, manuscript submitted to *Integers* (2026).

[Formalization and proof repository](https://github.com/gsidoine/coprime-adjacencies-lean).

For a permutation $a=(a_1,\ldots,a_n)$ of $\{1,\ldots,n\}$, let $c(a)$ be
the number of indices $i<n$ for which $\gcd(a_i,a_{i+1})=1$.
The minimum of $c(a)$ is determined exactly for $n\ge4$.
-/

@[expose] public section

namespace MinimumCoprimeAdjacencies

/-- The list contains every integer in $\{1,\ldots,n\}$ exactly once. -/
def IsPermutation (n : ℕ) (a : List ℕ) : Prop :=
  a.Perm (List.range' 1 n)

/-- The number of adjacent pairs with greatest common divisor one. -/
def adjacentCount (a : List ℕ) : ℕ :=
  (a.zip a.tail).countP (fun z => decide (Nat.Coprime z.1 z.2))

/-- The number of primes at most $n$. -/
def pi (n : ℕ) : ℕ := Nat.primeCounting n

/-- The right-hand side of the exact formula. Division on $\mathbb{N}$ is floor division. -/
def target (n : ℕ) : ℕ :=
  (pi n - pi (n / 2)) +
    max 1 (((pi (n / 2) - pi (n / 3)) + 1) / 2)

/-- The score $k$ occurs among permutations of $\{1,\ldots,n\}$. -/
def Attained (n k : ℕ) : Prop :=
  ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a = k

@[category API, AMS 5 11]
theorem attainable (n : ℕ) : ∃ k : ℕ, Attained n k := by
  refine ⟨adjacentCount (List.range' 1 n), List.range' 1 n, ?_, rfl⟩
  exact List.Perm.refl _

/-- The minimum number of adjacent coprime pairs over all permutations. -/
noncomputable def h (n : ℕ) : ℕ := by
  classical
  exact Nat.find (attainable n)

/-- For every $n\ge4$, the minimum number of coprime adjacencies is
$$
\pi(n)-\pi(n/2)+\max\left\{1,
  \left\lceil\frac{\pi(n/2)-\pi(n/3)}{2}\right\rceil\right\}.
$$
The prime-counting function is evaluated at real thresholds, so natural-number
floor division gives the same values. -/
@[category research solved, AMS 5 11]
theorem exact_minimum (n : ℕ) (hn : 4 ≤ n) :
    h n = target n := by
  sorry

end MinimumCoprimeAdjacencies

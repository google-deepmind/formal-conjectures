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
# Erdős Problem 21

*Reference:* [erdosproblems.com/21](https://www.erdosproblems.com/21)

Let $f(n)$ be the minimum size of an intersecting family of $n$-element sets such that every
set of size at most $n-1$ is disjoint from at least one member. Erdős and Lovász [ErLo75]
conjectured $f(n) = O(n)$, proved by Kahn [Ka94].

[ErLo75] Erdős, P. and Lovász, L., _Problems and results on 3-chromatic hypergraphs and some
related questions_. Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on
his 60th birthday), Vol. II (1975), 609–627.

[Ka92b] Kahn, J., _On a problem of Erdős and Lovász: Random methods in combinatorics_. Preprint
(1992).

[Ka94] Kahn, J., _On a problem of Erdős and Lovász II: $n(r) = O(r)$_. J. Amer. Math. Soc. **7**
(1994), no. 1, 125–143.
-/

namespace Erdos21

/--
A family $F$ of $n$-element subsets of $\mathbb{N}$ is intersecting if every two members
of $F$ have non-empty intersection.
-/
def IsIntersectingNFamily (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)

/--
A family $F$ of $n$-sets covers all small sets if every set $S$ with $|S| \leq n - 1$
is disjoint from at least one member of $F$.
-/
def CoversAllSmallSets (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/--
$f(n)$ is the minimal size of an intersecting family of $n$-sets that covers
all sets of size at most $n - 1$.
-/
noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset ℕ),
    F.card = k ∧ IsIntersectingNFamily F n ∧ CoversAllSmallSets F n}

/--
Let $f(n)$ be the minimal size of an intersecting family $F$ of $n$-element sets such that any
set $S$ with $|S| \leq n - 1$ is disjoint from at least one $A \in F$. Then $f(n) \ll n$, i.e.,
there exist constants $C > 0$ and $N_0$ such that $f(n) \leq C \cdot n$ for all $n \geq N_0$.

Erdős and Lovász [ErLo75] proved $(8/3)n - 3 \leq f(n) \ll n^{3/2} \log n$.
Kahn [Ka92b] improved the upper bound to $f(n) \ll n \log n$.
Kahn [Ka94] proved $f(n) \ll n$, settling the conjecture.
-/
@[category research solved, AMS 5]
theorem erdos_21 : answer(True) ↔
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (erdosLovaszF n : ℝ) ≤ C * n) := by
  sorry

end Erdos21

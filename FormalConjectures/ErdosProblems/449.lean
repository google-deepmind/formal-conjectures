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
# Erdős Problem 449

*References:*
- [erdosproblems.com/449](https://www.erdosproblems.com/449)
- [HaTe88] Hall, Richard R. and Tenenbaum, Gérald, *Divisors*. (1988), xvi+167.
- [Formal proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos449.lean)
-/

@[expose] public section

namespace Erdos449

/-- The number of divisor pairs $d_1 < d_2 < 2d_1$ of $n$. -/
def r (n : ℕ) : ℕ :=
  ((n.divisors.product n.divisors).filter fun p ↦
    p.1 < p.2 ∧ p.2 < 2 * p.1).card

/-- The empty divisor set of zero gives $r(0) = 0$. -/
@[category test, AMS 11]
theorem r_zero : r 0 = 0 := by decide

/-- The pair $(2,3)$ is the only pair counted by $r(6)$. -/
@[category test, AMS 11]
theorem r_six : r 6 = 1 := by decide

/--
Let $r(n)$ count the number of $d_1,d_2$ such that $d_1\mid n$ and $d_2\mid n$ and
$d_1<d_2<2d_1$. Is it true that, for every $\epsilon>0$,
\[r(n) < \epsilon \tau(n)\]
for almost all $n$, where $\tau(n)$ is the number of divisors of $n$?

This is false - indeed, for any constant $K>0$ we have $r(n)>K\tau(n)$ for a positive
density set of $n$. Kevin Ford has observed this follows from the negative solution to [448].
This argument is given for an essentially identical problem by Hall and Tenenbaum [HaTe88],
Section 4.6.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos449.lean#L361"]
theorem erdos_449 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (r n : ℝ) < ε * (n.divisors.card : ℝ)}.HasDensity 1 := by sorry

/-- For every $K > 0$, the set of $n$ with $r(n) > K\tau(n)$ contains a subset
of positive natural density. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos449.lean#L309"]
theorem erdos_449.variants.positive_density :
    ∀ K : ℝ, 0 < K → ∃ S : Set ℕ, S.HasPosDensity ∧
      S ⊆ {n : ℕ | K * (n.divisors.card : ℝ) < (r n : ℝ)} := by sorry

end Erdos449


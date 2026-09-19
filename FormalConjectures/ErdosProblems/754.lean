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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 754

*References:*
- [erdosproblems.com/754](https://www.erdosproblems.com/754)
- [Er94b] Erdős, Paul, _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261-269.
- [AEP88] Avis, David and Erdős, Paul and Pach, János, _Repeated distances in space_. Graphs
  Combin. (1988), 207--217.
- [Sw13] Swanepoel, Konrad J., _Favorite distances in high dimensions_. (2013), 499--519.
-/

@[expose] public section

open Filter

namespace Erdos754

open scoped Classical in
/-- `f n` is maximal such that there exists a set `A` of `n` points in $\mathbb{R}^4$ in which
every `x ∈ A` has at least `f n` points in `A` equidistant from `x` (i.e. at a common positive
distance from `x`). -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (EuclideanSpace ℝ (Fin 4)), A.card = n ∧
    ∀ x ∈ A, ∃ r > 0, k ≤ (A.filter fun y ↦ y ≠ x ∧ dist x y = r).card}

/--
Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^4$ in which
every $x\in A$ has at least $f(n)$ points in $A$ equidistant from $x$.

Is it true that $f(n)\leq \frac{n}{2}+O(1)$?

The answer is yes, proved by Swanepoel [Sw13]. Avis, Erdős, and Pach [AEP88] proved that
$\frac{n}{2}+2 \leq f(n) \leq (1+o(1))\frac{n}{2}$.
-/
@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos754.lean#L1205"]
theorem erdos_754 : answer(True) ↔ ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ n / 2 + C := by
  sorry

/-- Avis, Erdős, and Pach [AEP88] proved that $\frac{n}{2}+2 \leq f(n)$ for all large $n$. -/
@[category research solved, AMS 52]
theorem erdos_754.variants.lower_bound : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 + 2 ≤ f n := by
  sorry

open scoped Classical in
/--
Swanepoel [Sw13] in fact proved more generally that, in any finite set $A\subset \mathbb{R}^4$
of size $n$ and any choice of distance $d(x)$ for each $x\in A$,
$$\sum_{x\in A}\sum_{y\in A}1_{\lvert x-y\rvert =d(x)}\leq \tfrac{1}{2}n^2+O(n).$$
-/
@[category research solved, AMS 52]
theorem erdos_754.variants.swanepoel :
    ∃ C : ℝ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 4)))
      (d : EuclideanSpace ℝ (Fin 4) → ℝ),
      (∑ x ∈ A, ((A.filter fun y ↦ dist x y = d x).card : ℝ)) ≤
        (A.card : ℝ) ^ 2 / 2 + C * A.card := by
  sorry

end Erdos754

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
# Erdős Problem 1182

*Reference:* [erdosproblems.com/1182](https://www.erdosproblems.com/1182)
-/

open Filter SimpleGraph

namespace Erdos1182

open scoped Classical in
/--
$f(n)$ is the maximal number of edges in a connected graph $G$ on $n$ vertices such that
$R(K_3,G)=2n-1$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ G.edgeSet.ncard = m ∧
      graphRamsey (completeGraph (Fin 3)) G = 2 * n - 1}

open scoped Classical in
/--
$F(n)$ is the maximal $m\leq\binom{n}{2}$ such that every connected graph $G$ on $n$ vertices
with at most $m$ edges has $R(K_3,G)=2n-1$.

The bound $m\leq\binom{n}{2}$ keeps the set bounded above: without it, if every connected
$n$-vertex graph has this Ramsey number, then every $m$ would qualify and `sSup` on `ℕ`
would be $0$.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {m : ℕ | m ≤ n.choose 2 ∧ ∀ G : SimpleGraph (Fin n),
    G.Connected → G.edgeSet.ncard ≤ m →
      graphRamsey (completeGraph (Fin 3)) G = 2 * n - 1}

/--
Let $f(n)$ be maximal such that there is a connected graph $G$ with $n$ vertices and $f(n)$ edges
such that
$$R(K_3,G)= 2n-1.$$
Let $F(n)$ be maximal such that every connected graph $G$ with $n$ vertices and $\leq F(n)$ edges
has
$$R(K_3,G)= 2n-1.$$
Estimate $f(n)$ and $F(n)$.
-/
@[category research open, AMS 5]
theorem erdos_1182 :
    let growth : (ℕ → ℝ) × (ℕ → ℝ) := answer(sorry)
    (fun n ↦ (f n : ℝ)) =Θ[atTop] growth.1 ∧
    (fun n ↦ (F n : ℝ)) =Θ[atTop] growth.2 := by
  sorry

/--
In particular, is it true that $F(n)/n\to \infty$?

Brandt proved $F(n)\leq 84n$, so the answer is no.
-/
@[category research solved, AMS 5]
theorem erdos_1182.variants.F_div_n :
    answer(False) ↔ Tendsto (fun n : ℕ ↦ (F n : ℝ) / n) atTop atTop := by
  sorry

end Erdos1182

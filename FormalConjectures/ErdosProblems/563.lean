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
# Erdős Problem 563

*References:*
- [erdosproblems.com/563](https://www.erdosproblems.com/563)
- [Er90b] Erdős, Paul, Problems and results on graphs and hypergraphs: similarities and differences.
  Mathematics of Ramsey theory (1990), 12-28.
-/

open Filter

namespace Erdos563

open scoped Classical in
/--
A 2-coloring of $K_n$ (represented by graph $G$ on $\mathrm{Fin}\; n$) is balanced on subsets
of size at least $m$ with parameter $\alpha$ if every $X \subseteq [n]$ with $|X| \geq m$
contains more than $\alpha \binom{|X|}{2}$ edges of each color.
-/
def HasBalancedSubsets (n : ℕ) (m : ℕ) (α : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (X : Finset (Fin n)), m ≤ X.card →
    α * (X.card.choose 2 : ℝ) < ((G.induce (X : Set (Fin n))).edgeFinset.card : ℝ) ∧
    ((G.induce (X : Set (Fin n))).edgeFinset.card : ℝ) < (1 - α) * (X.card.choose 2 : ℝ)

open scoped Classical in
/--
$F(n,\alpha)$ is the smallest $m$ such that there exists a 2-coloring of the edges of $K_n$
so that every $X\subseteq [n]$ with $|X|\geq m$ contains more than $\alpha\binom{|X|}{2}$
edges of each color.
-/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf {m | ∃ (G : SimpleGraph (Fin n)), HasBalancedSubsets n m α G}

/--
Let $F(n,\alpha)$ denote the smallest $m$ such that there exists a $2$-colouring of the edges of
$K_n$ so that every $X\subseteq [n]$ with $\lvert X\rvert\geq m$ contains more than
$\alpha \binom{\lvert X\rvert}{2}$ many edges of each colour.

Prove that, for every $0\leq \alpha < 1/2$,
$$F(n,\alpha)\sim c_\alpha\log n$$
for some constant $c_\alpha$ depending only on $\alpha$.

This problem is #39 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_563 :
    ∀ (α : ℝ), 0 ≤ α → α < 1 / 2 →
      ∃ (c : ℝ), 0 < c ∧
        Tendsto (fun n : ℕ => (F n α : ℝ) / Real.log n) atTop (nhds c) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos563

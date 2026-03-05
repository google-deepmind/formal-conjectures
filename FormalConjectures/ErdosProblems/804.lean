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
# Erdős Problem 804

*Reference:* [erdosproblems.com/804](https://www.erdosproblems.com/804)

Let $f(m,n)$ be maximal such that any graph on $n$ vertices in which every induced
subgraph on $m$ vertices has an independent set of size at least $\log n$ must
contain an independent set of size at least $f(m,n)$.

Estimate $f(n)$. In particular, is it true that $f((\log n)^2, n) \geq n^{1/2 - o(1)}$?
Is it true that $f((\log n)^3, n) \gg (\log n)^3$?

A question of Erdős and Hajnal [Er91]. DISPROVED by Alon and Sudakov [AlSu07],
who proved that
$$(\log n)^2 / \log(\log n) \ll f((\log n)^2, n) \ll (\log n)^2$$
and
$$f((\log n)^3, n) \asymp (\log n)^2 / \log(\log n).$$
-/

open Classical SimpleGraph Finset

namespace Erdos804

/-- An independent set in a simple graph: a finset of vertices with no edges
    between any two of its members. -/
def IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

/-- The independence number of a graph on $n$ vertices: the maximum cardinality
    of an independent set. -/
noncomputable def independenceNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((univ : Finset (Fin n)).powerset.filter (IsIndepSet G)).sup Finset.card

/-- $f(m, n)$ is the largest $k$ such that every graph on $n$ vertices
    in which every induced subgraph on $m$ vertices has an independent set of
    size $\geq \lceil \log n \rceil$ must have independence number $\geq k$.

    Equivalently, the infimum of independence numbers over all qualifying
    graphs. -/
noncomputable def erdos804_f (m n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), S.card = m →
      ∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ Nat.ceil (Real.log (n : ℝ)) ∧
        IsIndepSet G T) ∧
    independenceNum G = k }

/--
Alon-Sudakov [AlSu07] upper bound: $f((\log n)^2, n) \leq C \cdot (\log n)^2$
for some constant $C > 0$ and all sufficiently large $n$.

This disproves the conjecture of Erdős and Hajnal that
$f((\log n)^2, n) \geq n^{1/2 - o(1)}$.
-/
@[category research solved, AMS 5]
theorem erdos_804 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 2)) n : ℝ) ≤
        C * (Real.log (n : ℝ)) ^ 2 := by
  sorry

/--
Alon-Sudakov [AlSu07] lower bound: $f((\log n)^2, n) \geq c \cdot (\log n)^2 / \log(\log n)$
for some constant $c > 0$ and all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_804.variants.part1_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 2)) n : ℝ) ≥
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) := by
  sorry

/--
Alon-Sudakov [AlSu07] upper bound: $f((\log n)^3, n) \leq C \cdot (\log n)^2 / \log(\log n)$
for some constant $C > 0$ and all sufficiently large $n$.

This disproves the conjecture of Erdős and Hajnal that
$f((\log n)^3, n) \gg (\log n)^3$.
-/
@[category research solved, AMS 5]
theorem erdos_804.variants.part2_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 3)) n : ℝ) ≤
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) := by
  sorry

/--
Alon-Sudakov [AlSu07] lower bound: $f((\log n)^3, n) \geq c \cdot (\log n)^2 / \log(\log n)$
for some constant $c > 0$ and all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_804.variants.part2_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 3)) n : ℝ) ≥
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) := by
  sorry

end Erdos804

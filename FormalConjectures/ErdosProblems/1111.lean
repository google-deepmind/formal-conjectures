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
# Erdős Problem 1111

*Reference:* [erdosproblems.com/1111](https://www.erdosproblems.com/1111)

For any $t, c \geq 1$, does there exist $d$ such that every finite graph with chromatic
number at least $d$ and clique number less than $t$ contains two anticomplete vertex sets
each with chromatic number at least $c$?

[ElEr85] El-Zahar, M. and Erdős, P., *On the existence of two nonneighboring
subgraphs in a graph*. Combinatorica **5** (1985), 295–300.

[Er85b] Erdős, P., *Problems and results on chromatic numbers in finite and infinite
graphs*. Graph theory with applications to algorithms and computer science
(Kalamazoo, Mich., 1984) (1985), 201–213.

[Wa80b] Wagon, S., *A bound on the chromatic number of graphs without certain
induced subgraphs*. J. Combin. Theory Ser. B **29** (1980), 345–346.

[NSS24] Nguyen, T., Scott, A. and Seymour, P., *On a problem of El-Zahar and
Erdős*. J. Combin. Theory Ser. B **165** (2024), 211–222.
-/

open SimpleGraph Classical

namespace Erdos1111

/-- Two disjoint sets of vertices $A$, $B$ are anticomplete in $G$ if there are no edges
between any vertex in $A$ and any vertex in $B$. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/--
Erdős Problem 1111 [ElEr85]:

If $t, c \geq 1$ then there exists $d \geq 1$ such that if $G$ is a finite graph with
$\chi(G) \geq d$ and $\omega(G) < t$, then there exist anticomplete sets
$A, B \subseteq V(G)$ with $\chi(G[A]) \geq c$ and $\chi(G[B]) \geq c$.

Two disjoint vertex sets $A$, $B$ are anticomplete if there are no edges between them.
$\chi$ denotes the chromatic number and $\omega$ the clique number. The condition
$\omega(G) < t$ is expressed as `G.CliqueFree t` (no clique of size $t$ exists).

El Zahar and Erdős show it suffices to consider $t \leq c$. Let $d(t,c)$ be the minimal
such $d$. Known bounds include $d(t,2) \leq \binom{t}{2}+1$ (via Wagon [Wa80b]) and
$d(3,3) \leq 8$.
-/
@[category research open, AMS 5]
theorem erdos_1111 (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (d : ℕ∞) ≤ G.chromaticNumber →
        G.CliqueFree t →
        ∃ (A B : Set (Fin n)),
          Anticomplete G A B ∧
          (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
          (c : ℕ∞) ≤ (G.induce B).chromaticNumber := by
  sorry

end Erdos1111

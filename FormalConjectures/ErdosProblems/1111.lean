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
# Erdős Problem 1111

*References:*
- [erdosproblems.com/1111](https://www.erdosproblems.com/1111)
- [ElEr85] El-Zahar, M. and Erdős, P., *On the existence of two nonneighboring subgraphs in a
  graph*. Combinatorica (1985), 295--300.
- [NSS24] Nguyen, Tung and Scott, Alex and Seymour, Paul, *On a problem of El-Zahar and Erdős*.
  J. Combin. Theory Ser. B (2024), 211--222.
- [Wa80b] Wagon, Stanley, *A bound on the chromatic number of graphs without certain induced
  subgraphs*. J. Combin. Theory Ser. B (1980), 345--346.
-/

namespace Erdos1111

open SimpleGraph

/--
If $G$ is a finite graph and $A,B$ are disjoint sets of vertices then we call $A,B$ anticomplete
if there are no edges between $A$ and $B$.
-/
def IsAnticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- The empty sets are anticomplete in any graph. -/
@[category test, AMS 5]
theorem isAnticomplete_empty {V : Type*} (G : SimpleGraph V) :
    IsAnticomplete G ∅ ∅ := by
  simp [IsAnticomplete]

/-- An edge forbids its endpoints from forming anticomplete singleton sets. -/
@[category test, AMS 5]
theorem not_isAnticomplete_of_adj {V : Type*} {G : SimpleGraph V} {a b : V}
    (h : G.Adj a b) : ¬ IsAnticomplete G {a} {b} := by
  intro hAB
  exact hAB.2 a (Set.mem_singleton a) b (Set.mem_singleton b) h

/--
`IsChromaticBound t c d` means that $d$ is admissible for $d(t,c)$: every finite graph $G$
with $\chi(G)\ge d$ and $\omega(G)<t$ has anticomplete vertex sets $A,B$ with
$\chi(A),\chi(B)\ge c$. Here $\chi(A)$ is the chromatic number of the induced subgraph $G[A]$,
and `G.CliqueFree t` is $\omega(G)<t$.
-/
def IsChromaticBound (t c d : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
      ∃ A B : Set V, IsAnticomplete G A B ∧
        (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        (c : ℕ∞) ≤ (G.induce B).chromaticNumber

/--
$d(t,c)$ is the least $d$ such that every finite graph $G$ with $\chi(G)\ge d$ and $\omega(G)<t$
has anticomplete sets $A,B$ with $\chi(A),\chi(B)\ge c$. This is $0$ if no such $d$ exists.
-/
noncomputable def d (t c : ℕ) : ℕ :=
  sInf {n | IsChromaticBound t c n}

/--
The minimum degree of the induced subgraph $G[A]$. This is $0$ if $A$ is empty, matching the
convention for `SimpleGraph.minDegree` on the empty vertex type.
-/
noncomputable def induceMinDegree {V : Type*} (G : SimpleGraph V) (A : Set V) : ℕ :=
  sInf ((fun a : V => (G.neighborSet a ∩ A).ncard) '' A)

/-- The empty induced subgraph has minimum degree $0$. -/
@[category test, AMS 5]
theorem induceMinDegree_empty {V : Type*} (G : SimpleGraph V) :
    induceMinDegree G (∅ : Set V) = 0 := by
  simp [induceMinDegree]

/--
If $t,c\geq 1$ then there exists $d\geq 1$ such that if $\chi(G)\geq d$ and $\omega(G)<t$ then
there are anticomplete sets $A,B$ with $\chi(A)\geq \chi(B)\geq c$.

A problem of El Zahar and Erdős [ElEr85], who show that it suffices to consider the case $t\leq c$.
-/
@[category research open, AMS 5]
theorem erdos_1111 (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d ≥ 1, IsChromaticBound t c d := by
  sorry

/--
El Zahar and Erdős [ElEr85] note that a result of Wagon [Wa80b] implies
$d(t,2)\leq \binom{t}{2}+1$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.wagon (t : ℕ) (ht : 1 ≤ t) :
    IsChromaticBound t 2 (t.choose 2 + 1) := by
  sorry

/--
In fact $d(t+1,2)\leq d(t,2)+t$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.wagon_recurrence (t : ℕ) :
    d (t + 1) 2 ≤ d t 2 + t := by
  sorry

/-- We have $d(2,2)=2$. The source writes $t(2,2)=2$. -/
@[category research solved, AMS 5]
theorem erdos_1111.variants.d_two_two : d 2 2 = 2 := by
  sorry

/-- We have $d(3,2)=4$. The source writes $t(3,2)=4$. -/
@[category research solved, AMS 5]
theorem erdos_1111.variants.d_three_two : d 3 2 = 4 := by
  sorry

/-- We have $d(4,2)=5$. The source writes $t(4,2)=5$. -/
@[category research solved, AMS 5]
theorem erdos_1111.variants.d_four_two : d 4 2 = 5 := by
  sorry

/-- El Zahar and Erdős [ElEr85] proved $d(3,3)\leq 8$. -/
@[category research solved, AMS 5]
theorem erdos_1111.variants.d_three_three : IsChromaticBound 3 3 8 := by
  sorry

/--
El Zahar and Erdős [ElEr85] proved
$$
d(t,3) \leq 2\binom{t-1}{3}+7\binom{t-1}{2}+t
$$
for $t>3$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.d_t_three (t : ℕ) (ht : 3 < t) :
    IsChromaticBound t 3 (2 * (t - 1).choose 3 + 7 * (t - 1).choose 2 + t) := by
  sorry

/--
Nguyen, Scott, and Seymour [NSS24] prove that if $t,c\geq 1$ then there exists $d\geq 1$ such
that if $\chi(G)\geq d$ and $\omega(G)<t$ then there are anticomplete sets $A,B$ with
$\chi(B)\geq c$ and such that the minimum degree of the induced graph on $A$ is at least $c$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.nguyen_scott_seymour (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d ≥ 1, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, IsAnticomplete G A B ∧
          c ≤ induceMinDegree G A ∧
          (c : ℕ∞) ≤ (G.induce B).chromaticNumber := by
  sorry

end Erdos1111

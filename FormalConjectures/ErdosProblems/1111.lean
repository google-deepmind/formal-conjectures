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
# Erdős Problem 1111

*References:*
- [erdosproblems.com/1111](https://www.erdosproblems.com/1111)
- [ElEr85] El-Zahar, M. and Erdős, P., *On the existence of two non-neighboring subgraphs in a
  graph*. Combinatorica 5 (1985), 295-300.
- [NSS24] Nguyen, T., Scott, A. and Seymour, P., *On a problem of El-Zahar and Erdős*.
  J. Combin. Theory Ser. B 165 (2024), 211-222. [arXiv:2303.13449](https://arxiv.org/abs/2303.13449)
- [Wa80b] Wagon, S., *A bound on the chromatic number of graphs without certain induced
  subgraphs*. J. Combin. Theory Ser. B 29 (1980), 345-346.
-/

@[expose] public section

namespace Erdos1111

/-- Two sets `A` and `B` of vertices of `G` are *anticomplete* if they are disjoint and `G` has
no edge between `A` and `B`. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- Anticomplete sets stay anticomplete when the two sets are swapped. -/
@[category API, AMS 5]
theorem Anticomplete.symm {V : Type*} {G : SimpleGraph V} {A B : Set V}
    (h : Anticomplete G A B) : Anticomplete G B A := by
  obtain ⟨hd, h⟩ := h
  exact ⟨hd.symm, fun b hb a ha hba ↦ h a ha b hb hba.symm⟩

/--
If $G$ is a finite graph and $A,B$ are disjoint sets of vertices then we call $A,B$ anticomplete
if there are no edges between $A$ and $B$.

If $t,c\geq 1$ then there exists $d\geq 1$ such that if $\chi(G)\geq d$ and $\omega(G)<t$ then
there are anticomplete sets $A,B$ with $\chi(A)\geq \chi(B)\geq c$.

El-Zahar and Erdős [ElEr85] pose this as a question. Here $\chi(A)$ is the chromatic number of
the induced subgraph $G[A]$. Swapping $A$ and $B$, the conclusion says that both $\chi(A)$ and
$\chi(B)$ are at least $c$.
-/
@[category research open, question, AMS 5]
theorem erdos_1111 :
    ∀ t c : ℕ, 1 ≤ t → 1 ≤ c → ∃ d : ℕ, 1 ≤ d ∧
      ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
        (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
          ∃ A B : Set V, Anticomplete G A B ∧
            (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
            (c : ℕ∞) ≤ (G.induce B).chromaticNumber := by
  sorry

/--
El-Zahar and Erdős note that a result of Wagon [Wa80b] implies $d(t,2)\leq \binom{t}{2}+1$, where
$d(t,c)$ is the minimal $d$ in the problem.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.wagon (t : ℕ) :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, Anticomplete G A B ∧
          2 ≤ (G.induce A).chromaticNumber ∧ 2 ≤ (G.induce B).chromaticNumber := by
  sorry

/--
El-Zahar and Erdős [ElEr85] proved the case $c = 3$: $d(t,3)$ exists for every $t$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.el_zahar_erdos :
    ∀ t : ℕ, 1 ≤ t → ∃ d : ℕ, 1 ≤ d ∧
      ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
        (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
          ∃ A B : Set V, Anticomplete G A B ∧
            3 ≤ (G.induce A).chromaticNumber ∧ 3 ≤ (G.induce B).chromaticNumber := by
  sorry

/--
El-Zahar and Erdős [ElEr85] proved $d(3,3)\leq 8$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.three_three :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      8 ≤ G.chromaticNumber → G.CliqueFree 3 →
        ∃ A B : Set V, Anticomplete G A B ∧
          3 ≤ (G.induce A).chromaticNumber ∧ 3 ≤ (G.induce B).chromaticNumber := by
  sorry

/--
Nguyen, Scott, and Seymour [NSS24] prove that if $t,c\geq 1$ then there exists $d\geq 1$ such
that if $\chi(G)\geq d$ and $\omega(G)<t$ then there are anticomplete sets $A,B$ with
$\chi(B)\geq c$ and such that the minimum degree of the induced graph on $A$ is at least $c$.
-/
@[category research solved, AMS 5]
theorem erdos_1111.variants.nguyen_scott_seymour :
    ∀ t c : ℕ, 1 ≤ t → 1 ≤ c → ∃ d : ℕ, 1 ≤ d ∧
      ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
        (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
          ∃ A B : Set V, Anticomplete G A B ∧
            A.Nonempty ∧ (∀ v ∈ A, c ≤ (A ∩ G.neighborSet v).ncard) ∧
            (c : ℕ∞) ≤ (G.induce B).chromaticNumber := by
  sorry

end Erdos1111

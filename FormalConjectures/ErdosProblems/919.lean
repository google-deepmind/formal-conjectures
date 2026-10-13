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
# Erdős Problem 919

*References:*
- [erdosproblems.com/919](https://www.erdosproblems.com/919)
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [ErHa68b] Erdős, P. and Hajnal, A., On chromatic number of infinite graphs. (1968), 83--98.
- [Ba84] Baumgartner, J. E., Generic graph construction. J. Symbolic Logic (1984), 234--240.
- [FoLa88] Foreman, M. and Laver, R., Some downwards transfer properties for $\aleph_2$.
  Adv. in Math. (1988), 230--238.
- [Sh90] Shelah, S., Incompactness for chromatic numbers of graphs. A tribute to Paul Erdős,
  Cambridge Univ. Press (1990), 361--371.
-/

@[expose] public section

universe u

open Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos919

-- The question is independent of ZFC (see the docstring), so the answer stays a placeholder.
set_option linter.style.category_answer false in
/--
Is there a graph $G$ with vertex set $\omega_2^2$ and chromatic number $\aleph_2$ such that every
subgraph whose vertices have a lesser type has chromatic number $\leq \aleph_0$?

The vertex set is the ordinal $\omega_2^2$ with its usual order, and a set of vertices has lesser
type when its order type is less than $\omega_2^2$. A subgraph on a vertex set has chromatic
number at most that of the induced subgraph, so the statement uses induced subgraphs.

This question is **independent of ZFC**, relative to a huge cardinal, so the answer stays
`answer(sorry)`. By `erdos_919.variants.iff_erdos_918_i` it is equivalent in ZFC to the first
question of Problem 918 (`Erdos918.erdos_918.parts.i`): is there a graph with $\aleph_2$ vertices
and chromatic number $\aleph_2$ all of whose subgraphs on $\aleph_1$ vertices have chromatic
number $\leq \aleph_0$? Such a graph exists if $V = L$ [Sh90] and in a model of GCH due to
Baumgartner [Ba84]. Foreman and Laver [FoLa88] showed, starting from a huge cardinal, that it is
consistent with GCH that no such graph exists.
-/
@[category research solved, AMS 3 5]
theorem erdos_919 : answer(sorry) ↔
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
What if instead we ask for $G$ to have chromatic number $\aleph_1$?

By `erdos_919.variants.aleph_1_iff` this asks whether there is a graph on $\aleph_2$ vertices with
uncountable chromatic number all of whose subgraphs on $\aleph_1$ vertices have chromatic number
$\leq \aleph_0$. The answer is yes under CH (`erdos_919.variants.aleph_1_of_CH`) and whenever
the $\aleph_2$ question has a positive answer (`erdos_919.variants.aleph_2_imp_aleph_1`).
-/
@[category research open, AMS 3 5]
theorem erdos_919.variants.aleph_1 : answer(sorry) ↔
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
The $\aleph_2$ question is equivalent to the first question of Problem 918
(`Erdos918.erdos_918.parts.i`). A graph on $\aleph_2$ vertices is moved to $\omega_2$, and each
vertex $\xi$ is replaced by the row $\{\xi\} \times \omega_2$ of $\omega_2 \times \omega_2$ in the
lexicographic order. Two vertices $(\xi, \eta)$ and $(\xi', \eta')$ with $\xi < \xi'$ are joined
when $\xi$ and $\xi'$ are joined and $\eta \geq \xi'$.
-/
@[category research solved, AMS 3 5, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/e7de340be9c1828da18538feb254ee9dfcf3af42/ErdosLean/Erdos919.lean#L848"]
theorem erdos_919.variants.iff_erdos_918_i :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
The $\aleph_1$ question is equivalent to the existence of a graph on $\aleph_2$ vertices with
chromatic number $> \aleph_0$ all of whose subgraphs on $\aleph_1$ vertices have chromatic number
$\leq \aleph_0$.
-/
@[category research solved, AMS 3 5, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/e7de340be9c1828da18538feb254ee9dfcf3af42/ErdosLean/Erdos919.lean#L859"]
theorem erdos_919.variants.aleph_1_iff :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
A positive answer to the $\aleph_2$ question gives a positive answer to the $\aleph_1$ question.
-/
@[category research solved, AMS 3 5, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/e7de340be9c1828da18538feb254ee9dfcf3af42/ErdosLean/Erdos919.lean#L869"]
theorem erdos_919.variants.aleph_2_imp_aleph_1 :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) →
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
Under the continuum hypothesis the $\aleph_1$ question has a positive answer. The shift graph on
$\omega_2$ of Erdős and Hajnal [ErHa68b] is not countably chromatic when
$2^{\aleph_0} = \aleph_1$, and its subgraphs on $\aleph_1$ vertices have chromatic number
$\leq \aleph_0$.
-/
@[category research solved, AMS 3 5, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/e7de340be9c1828da18538feb254ee9dfcf3af42/ErdosLean/Erdos919.lean#L883"]
theorem erdos_919.variants.aleph_1_of_CH (hCH : 𝔠 = ℵ₁) :
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

end Erdos919

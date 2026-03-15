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
# Erdős Problem 1035

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)

Is there a constant $c > 0$ such that every graph on $2^n$ vertices with minimum degree
$> (1 - c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$ as a subgraph?

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.
-/

open SimpleGraph Finset

namespace Erdos1035

/-- The $n$-dimensional hypercube graph $Q_n$: vertices are functions `Fin n → Bool`,
and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless v h := h.1 rfl

/-- An injective graph homomorphism from $H$ to $G$: $G$ contains a copy of $H$
as a subgraph. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Conjecture (Problem 1035) [Er93, p.345]:

Is there a constant $c > 0$ such that every graph on $2^n$ vertices with
minimum degree $> (1 - c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$?

Formulated as: there exists $c > 0$ such that for all $n$ and for every graph $G$
on $2^n$ vertices, if every vertex has degree $> (1 - c) \cdot 2^n$, then $G$ contains
a copy of $Q_n$ as a subgraph.
-/
@[category research open, AMS 5]
theorem erdos_1035 : answer(sorry) ↔
    (∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ,
    ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
      (∀ v : Fin (2 ^ n),
        (G.degree v : ℝ) > (1 - c) * (2 ^ n : ℝ)) →
      ContainsSubgraph G (hypercubeGraph n)) := by
  sorry

end Erdos1035

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
# The van Dam–Haemers conjecture

*Reference:* [Koval and Kwan, Conjecture 1.2](https://arxiv.org/html/2309.09788v2#S1).

A finite simple graph is determined by its adjacency spectrum if every finite simple graph
with the same adjacency spectrum is isomorphic to it. The spectrum counts eigenvalues
with multiplicity.

As $n \to \infty$, the proportion of unlabelled simple graphs on $n$ vertices that are
determined by their adjacency spectrum tends to $1$. Each isomorphism class is counted once.

Each spectrum realized by a spectrum-determined graph corresponds to exactly one isomorphism
class. The denominator uses the asymptotic count $2^{\binom{n}{2}}/n!$ of unlabelled graphs.
-/

@[expose] public section

namespace Arxiv.«2309.09788»

open scoped Classical in
/-- The characteristic polynomial of the adjacency matrix over the integers. -/
noncomputable def adjacencyPolynomial {n : Nat} (G : SimpleGraph (Fin n)) : Polynomial Int :=
  (G.adjMatrix Int).charpoly

/-- Every graph on the same vertex type with the same adjacency spectrum is isomorphic to
the given graph. -/
def IsDeterminedBySpectrum {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n),
    adjacencyPolynomial G = adjacencyPolynomial H → Nonempty (SimpleGraph.Iso G H)

/-- The adjacency spectra of graphs on `n` vertices that are determined by their spectra. -/
def determinedSpectra (n : Nat) : Set (Polynomial Int) :=
  Set.image adjacencyPolynomial {G : SimpleGraph (Fin n) | IsDeterminedBySpectrum G}

/-- The proportion of unlabelled graphs determined by their adjacency spectrum tends to one
as the number of vertices tends to infinity. -/
@[category research open, AMS 5]
theorem van_dam_haemers_conjecture :
    Filter.Tendsto (fun n : ℕ =>
      ((determinedSpectra n).ncard : ℝ) / ((2 : ℝ) ^ (Nat.choose n 2) / (Nat.factorial n : ℝ)))
      Filter.atTop (nhds (1 : ℝ)) := by
  sorry

end Arxiv.«2309.09788»

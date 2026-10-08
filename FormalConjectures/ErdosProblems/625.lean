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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 625

*Reference:* [erdosproblems.com/625](https://www.erdosproblems.com/625)
-/
universe u
variable {V : Type}

private noncomputable abbrev χ (G : SimpleGraph V) : ℕ := G.chromaticNumber.toNat

private noncomputable abbrev ζ (G : SimpleGraph V) : ℕ := G.cochromaticNumber.toNat

open scoped MeasureTheory

open scoped NNReal


open PMF BigOperators

variable (V : Type*) [Fintype V] [DecidableEq V]

namespace SimpleGraph


/--
The Erdős-Rényi random graph model G(n, p), defined as a probability
mass function (`PMF`) on `SimpleGraph V`.

Each of the `N = Fintype.card (Sym2 V)` possible edges is included in the
graph independently with probability `p`.
-/
noncomputable def erdosRenyi (p : ENNReal) (hp : p <= 1) : PMF (SimpleGraph V) :=
  -- Define the probability for a *single* function `g : Sym2 V → Bool`.
  -- This is the product of the probabilities of each choice `g e`.
  let edgeChoicesProb (g : Sym2 V → Bool) : ENNReal :=
    ∏ e ∈ (⊤ : Finset (Sym2 V)), bernoulli p hp (g e)

  letI edgeChoicesPMF : PMF (Sym2 V → Bool) :=
    ofFintype (edgeChoicesProb) (by sorry)

  -- Define the function to convert edge choices into a SimpleGraph.
  letI toGraph (f : Sym2 V → Bool) : SimpleGraph V :=
    SimpleGraph.fromEdgeSet {e | f e}

  -- Finally, `map` the PMF over choices to the PMF over graphs.
  edgeChoicesPMF.map toGraph

end SimpleGraph

open Filter SimpleGraph
open scoped Topology

/--
If $G$ is a random graph with $n$ vertices and each edge included
independently with probability $\frac 1 2$ then is it true that almost
surely $χ(G) - ζ(G) → \infty$ as $n → \infty$?
-/
@[category research open, AMS 5]
theorem erdos_625 :
    (∃ select_almost_all_graphs :  Π (n : ℕ), Set (SimpleGraph (Fin n)),
    atTop.Tendsto (fun i =>
      letI μ := (erdosRenyi (Fin i) (1/2) (by norm_num)).toOuterMeasure
      (μ (select_almost_all_graphs i)))  (𝓝 1) ∧
    ∀ select_any_from_set : Π (n : ℕ), SimpleGraph (Fin n),
    ∀ i, select_any_from_set i ∈ select_almost_all_graphs i →
    atTop.Tendsto (fun i =>
      letI G := select_any_from_set i
      χ G - χ G
      ) atTop) ↔ answer(sorry)
    := by
  sorry

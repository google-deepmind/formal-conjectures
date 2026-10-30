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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Max

/-!
# Smallest mode of the degree sequence

The tie rule is WOWII definition 45: select the smallest most frequent degree.
The empty graph has no degree mode; its numerical value is set to zero.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degrees with maximum frequency among the degrees occurring in the graph. -/
def degreeModes (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.image (fun v : V => G.degree v)).filter fun d =>
    ∀ w : V,
      (Finset.univ.filter fun v => G.degree v = G.degree w).card ≤
        (Finset.univ.filter fun v => G.degree v = d).card

/-- The smallest most frequent degree, or zero for the empty graph. -/
def smallestDegreeMode (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (degreeModes G).min.getD 0

end SimpleGraph

example : (⊥ : SimpleGraph (Fin 0)).smallestDegreeMode = 0 := by decide
example : (⊥ : SimpleGraph (Fin 1)).smallestDegreeMode = 0 := by decide

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
import Mathlib.Topology.Basic

/-!
# Erdős Problem 1092

*Reference:* https://www.erdosproblems.com/1092


If a graph `G` has the property that every subgraph `H` on `m` vertices can be
written as the union of
1. a graph of chromatic number at most `r`, and
2. a graph with at most `f r m` edges,

then `G` has chromatic number at most `r + 1`.

Erdős asked whether:
* `f 2 n ≫ n`
* more generally, `f r n ≫ r * n`

This problem is currently open.
-/

namespace Erdos1092

open Classical
open SimpleGraph
open Finset

/--
Asymptotic domination: `f ≫ g` means `g n / f n → 0`.
This is the standard Erdős-style notation.
-/
def dominates (f g : ℕ → ℕ) : Prop :=
  tendsto (fun n => (g n : ℝ) / (f n : ℝ)) atTop (nhds 0)

notation f " ≫ " g => dominates f g

/--
Erdős Problem 1092 (open).

There exists a function `f : ℕ → ℕ → ℕ` such that:
* If every subgraph of a graph `G` can be decomposed into an `r`-colorable part
  and a sparse remainder with at most `f r m` edges,
  then `G` has chromatic number at most `r + 1`.
* Moreover, `f 2 n ≫ n`.
* More generally, `f r n ≫ fun n => r * n`.
-/
@[category research open, AMS 5]
theorem erdos_1092 :
  (∃ f : ℕ → ℕ → ℕ,
    (∀ r n, 0 ≤ f r n) ∧
    (∀ r n,
      ∀ G : SimpleGraph (Fin n),
        (∀ H : Subgraph G,
          let m := H.verts.toFinset.card
          ∃ H₁ H₂ : Subgraph H.coe,
            chromaticNumber H₁.coe ≤ r ∧
            H₂.edgeSet.toFinset.card ≤ f r m) →
        chromaticNumber G ≤ r + 1) ∧
    dominates (fun n => f 2 n) (fun n => n) ∧
    (∀ r, dominates (fun n => f r n) (fun n => r * n)))
  ↔ answer(sorry) := by
  sorry

end Erdos1092

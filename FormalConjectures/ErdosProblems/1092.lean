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
open Asymptotics
open Filter

/--
The function `f : ℕ → ℕ → ℕ` with the Erdős 1092 properties.
Defined as the supremum over all functions satisfying the chromatic number decomposition property.
-/
noncomputable def f : ℕ → ℕ → ℕ :=
  sSup {g : ℕ → ℕ → ℕ |
    ∀ (r : ℕ) (n : ℕ),
      ∀ G : SimpleGraph (Fin n),
        (∀ H : Subgraph G,
          let m := H.verts.toFinset.card
          ∃ H₁ H₂ : Subgraph H.coe,
            chromaticNumber H₁.coe ≤ (r : ℕ∞) ∧
            H₂.edgeSet.toFinset.card ≤ g r m) →
        chromaticNumber G ≤ (r + 1 : ℕ∞)}

/--
Erdős Problem 1092 (open).

There exists a function `f : ℕ → ℕ → ℕ` such that:
* If every subgraph of a graph `G` can be decomposed into an `r`-colorable part
  and a sparse remainder with at most `f r m` edges,
  then `G` has chromatic number at most `r + 1`.
* Moreover, `(fun n => n) =o[atTop] (fun n => f 2 n)`.
* More generally, `∀ r, (fun n => r * n) =o[atTop] (fun n => f r n)`.
-/
@[category research open, AMS 5]
theorem erdos_1092 :
  ((∀ r n, 0 ≤ f r n) ∧
    (∀ (r : ℕ) (n : ℕ),
      ∀ G : SimpleGraph (Fin n),
        (∀ H : Subgraph G,
          let m := H.verts.toFinset.card
          ∃ H₁ H₂ : Subgraph H.coe,
            chromaticNumber H₁.coe ≤ (r : ℕ∞) ∧
            H₂.edgeSet.toFinset.card ≤ f r m) →
        chromaticNumber G ≤ (r + 1 : ℕ∞)) ∧
    (fun (n : ℕ) => (n : ℝ)) =o[atTop] (fun (n : ℕ) => (f 2 n : ℝ)) ∧
    (∀ (r : ℕ), (fun (n : ℕ) => (r * n : ℝ)) =o[atTop] (fun (n : ℕ) => (f r n : ℝ))))
  ↔ answer(sorry) := by
  sorry

end Erdos1092

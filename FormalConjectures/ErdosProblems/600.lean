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
# Erdős Problem 600
*Reference:*
- [erdosproblems.com/600](https://www.erdosproblems.com/600)
- [RuSz78] Ruzsa, I. Z. and Szemerédi, E., Triple systems with no six points carrying three triangles. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978), 939-945.
-/

open Classical Filter
open scoped Topology

namespace Erdos600

/--
Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles.
-/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e ∧
  (∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e.toFinset ⊆ t) →
  (∃ e ∈ G.edgeFinset, ∃ S ⊆ G.cliqueFinset 3, ∀ t ∈ S, e.toFinset ⊆ t ∧ S.card ≥ r)

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

/--
Let $r \geq 2$. Is it true that $e(n,r+1) - e(n,r) \to \infty$ as $n \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_600.parts.i :
    answer(sorry) ↔ ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun (n : ℕ) ↦ eFunction n (r + 1) - eFunction n r) atTop atTop := by
  sorry

/--
Let $r \geq 2$. Is it true that $\frac{e(n,r+1)}{e(n,r)} \to 1$ as $n \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_600.parts.ii :
    answer(sorry) ↔ ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun (n : ℕ) ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (𝓝 1) := by
  sorry

/--
Ruzsa and Szemerédi [RuSz78] proved that $e(n,r)=o(n^2)$ for any fixed $r$.
-/
@[category research solved, AMS 11]
theorem erdos_600.variants.ruzsa_szemeredi_upper_bound :
    ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n^2 : ℝ)) := by
  sorry

end Erdos600

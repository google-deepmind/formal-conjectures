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
# Erdős Problem 1167

*Reference:* [erdosproblems.com/1167](https://www.erdosproblems.com/1167)

A problem of Erdős, Hajnal, and Rado on cardinal partition relations:
does the stepping-up lemma hold for partition relations, i.e., does
$2^\lambda \to (\kappa_\alpha + 1)^{r+1}$ imply $\lambda \to (\kappa_\alpha)^r$
for $r \geq 2$ and $\lambda$ infinite?

[Va99] Vaughan, J., *Small uncountable cardinals and topology*. Open Problems in Topology (1999).
-/

open Cardinal

namespace Erdos1167

/-- The cardinal partition relation $\kappa \to (\text{targets}(\alpha))_{\alpha : \iota}^r$:
    for every coloring of the $r$-element subsets of a $\kappa$-sized set with colors from $\iota$,
    there exists a color $i$ and a monochromatic subset of cardinality $\geq \text{targets}(i)$. -/
def CardinalPartitionRel (κ : Cardinal) {ι : Type*} (targets : ι → Cardinal)
    (r : ℕ) : Prop :=
  ∀ (S : Type*) [DecidableEq S] (_ : #S = κ) (c : Finset S → ι),
    ∃ (i : ι) (H : Set S),
      Cardinal.mk H ≥ targets i ∧
      ∀ s : Finset S, s.card = r → (↑s : Set S) ⊆ H → c s = i

/-- **Erdős Problem 1167** [Va99, 7.79] (Erdős–Hajnal–Rado):
    For $r \geq 2$ and $\lambda$ infinite, does
    $2^\lambda \to (\kappa_\alpha + 1)^{r+1}$ imply $\lambda \to (\kappa_\alpha)^r$? -/
@[category research open, AMS 3 5]
theorem erdos_1167 : answer(sorry) ↔
    ∀ {ι : Type*} (κ : ι → Cardinal) (lam : Cardinal) (r : ℕ),
      r ≥ 2 → ℵ₀ ≤ lam →
      CardinalPartitionRel ((2 : Cardinal) ^ lam) (fun α => κ α + 1) (r + 1) →
      CardinalPartitionRel lam κ r := by
  sorry

end Erdos1167

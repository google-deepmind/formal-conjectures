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
# A linear list-colouring bound in the Hadwiger number

*Reference:* OpenAI, *A linear list-coloring bound in terms of the Hadwiger number* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf
-/

@[expose] public section

namespace LinearListHadwiger

open SimpleGraph

/-- There is a universal integer $C \geq 1$ such that every finite nonempty graph satisfies
$\chi_{\mathrm{list}}(G) \leq C h(G)$, where $h(G)$ is its Hadwiger number. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Main.lean#L58"]
theorem linear_list_hadwiger :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      listChromaticNumber G ≤ C * hadwigerNumber G := by
  sorry

end LinearListHadwiger

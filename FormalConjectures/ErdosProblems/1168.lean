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
# Erdős Problem 1168

*Reference:* [erdosproblems.com/1168](https://www.erdosproblems.com/1168)

A problem of Erdős, Hajnal, and Rado on the negative partition relation
$\aleph_{\omega+1} \nrightarrow (\aleph_{\omega+1}, 3, \ldots, 3)_{\aleph_0}^2$
without assuming the generalised continuum hypothesis.

[Va99] Vaughan, J., *Small uncountable cardinals and topology*. Open Problems in Topology (1999).
-/

open Cardinal Ordinal

namespace Erdos1168

/--
Erdős Problem 1168 [Va99, 7.80]:

The negative partition relation
$\aleph_{\omega+1} \nrightarrow (\aleph_{\omega+1}, 3, \ldots, 3)_{\aleph_0}^2$:
for any type $\alpha$ of cardinality $\aleph_{\omega+1}$, there exists a coloring of unordered
pairs of elements of $\alpha$ with countably many colors (indexed by $\mathbb{N}$) such that:
- No set of cardinality $\aleph_{\omega+1}$ is monochromatic in color $0$
- No triple is monochromatic in any color $n \geq 1$
-/
@[category research open, AMS 3 5]
theorem erdos_1168 :
    ∀ (α : Type*) (_ : #α = ℵ_ (ω + 1)),
    ∃ (c : α → α → ℕ),
      -- The coloring is symmetric
      (∀ a b, c a b = c b a) ∧
      -- No monochromatic set of cardinality ℵ_{ω+1} for color 0
      (∀ S : Set α, #S = ℵ_ (ω + 1) →
        ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ c a b ≠ 0) ∧
      -- No monochromatic triple for any color n ≥ 1
      (∀ (n : ℕ), n ≥ 1 →
        ∀ a b d : α, a ≠ b → a ≠ d → b ≠ d →
          ¬(c a b = n ∧ c a d = n ∧ c b d = n)) := by
  sorry

end Erdos1168

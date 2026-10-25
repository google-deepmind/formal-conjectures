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
# Erdős Problem 183

*References:*
- [erdosproblems.com/183](https://www.erdosproblems.com/183)
- [Er61] Erdős, P., *Graph theory and probability. II*. Canad. J. Math. (1961), 346-352.
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science*. (2026).
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos183

/--
Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours
then there must exist a monochromatic triangle. Determine
$$\lim_{k\to \infty}R(3;k)^{1/k}.$$

There is no finite limit: $R(3;k)^{1/k}\to\infty$. This was established by OpenAI [OpenAI26]
along with the explicit superexponential lower bound in
`erdos_183.variants.explicit_lower_bound`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean"]
theorem erdos_183 :
    Tendsto (fun k : ℕ => (SimpleGraph.cliqueRamseyNumber (fun _ : Fin k ↦ 3) : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  sorry

/--
The explicit bound behind `erdos_183`: for every $k\geq 2$,
$$R(3;k)\geq \left(\frac{k^{1/3}}{6e^{38}\log k}\right)^k.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean"]
theorem erdos_183.variants.explicit_lower_bound :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (SimpleGraph.cliqueRamseyNumber (fun _ : Fin k ↦ 3) : ℝ) := by
  sorry

end Erdos183

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

import FormalConjecturesUtil

/-!
# Erdős Problem 146

*References:*
- [erdosproblems.com/146](https://www.erdosproblems.com/146)
- [ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related problems*.
  Progress in graph theory (1984), 203-218.
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science*. (2026).
-/

open Filter SimpleGraph

namespace Erdos146

open scoped Classical in
/-- The neighbours of `v` lying inside `s`. -/
noncomputable def neighborsWithin {V : Type*} (H : SimpleGraph V) (s : Finset V) (v : V) :
    Finset V := s.filter (H.Adj v)

/-- `H` is `r`-degenerate when every induced subgraph has a vertex of degree at most `r`, that is,
every nonempty vertex set contains a vertex with at most `r` neighbours inside it. -/
def IsDegenerate {V : Type*} (r : ℕ) (H : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (neighborsWithin H s v).card ≤ r

/--
If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has minimum
degree $\leq r$, then
$$\mathrm{ex}(n;H) \ll n^{2-1/r}.$$

The answer is no. OpenAI [OpenAI26] give a connected bipartite `2`-degenerate `H` and constants
`c, ε > 0` with $\mathrm{ex}(n;H)\geq cn^{3/2+\epsilon}$ for all large `n`, which exceeds the
conjectured $n^{2-1/2}=n^{3/2}$. See `erdos_146.variants.two_degenerate_counterexample`.
-/
@[category research solved, AMS 5]
theorem erdos_146 : answer(False) ↔
    ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
      0 < r → H.IsBipartite → IsDegenerate r H →
        Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n H : ℝ))
          (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ))) := by
  sorry

/--
The counterexample: a connected bipartite `2`-degenerate `H` whose extremal number exceeds
$n^{3/2+\epsilon}$ infinitely often, so the `r = 2` case of `erdos_146` fails.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean"]
theorem erdos_146.variants.two_degenerate_counterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate 2 H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤ (extremalNumber n H : ℝ) := by
  sorry

end Erdos146

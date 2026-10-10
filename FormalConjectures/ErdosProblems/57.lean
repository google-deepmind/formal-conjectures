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
# Erdős Problem 57

*References:*
- [erdosproblems.com/57](https://www.erdosproblems.com/57)
- [ErHa66] Erdős, P. and Hajnal, A., *On chromatic number of graphs and set-systems*.
  Acta Math. Acad. Sci. Hungar. (1966), 61-99.
- [LiMo20] Liu, Hong and Montgomery, Richard, *A solution to Erdős and Hajnal's odd cycle problem*.
  arXiv:2010.15802 (2020).
-/

@[expose] public section

namespace Erdos57

/--
If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are lengths of the odd
cycles of $G$ then $\sum \frac{1}{a_i} = \infty$.

Conjectured by Erdős and Hajnal [ErHa66], and solved by Liu and Montgomery [LiMo20].

The linked formal proof (Codex and GPT-5.6 Sol) states the conclusion as
`¬ Summable (oddCycleReciprocal G)`, where `oddCycleReciprocal G n` is `n⁻¹` if `n` is an odd
cycle length of `G` and `0` otherwise; this is the indicator form of the sum below.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos57.lean#L11124"]
theorem erdos_57 :
    ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
      ¬ Summable (fun (a : G.oddCycleLengths) ↦ 1 / (a : ℝ)) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos57

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
# Erdős Problem 181

*References:*
- [erdosproblems.com/181](https://www.erdosproblems.com/181)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Ti22] Tikhomirov, K., *A remark on the Ramsey number of the hypercube*. arXiv:2208.14568 (2022).
- [OpenAI26] OpenAI, *The hypercube Ramsey number has linear order*. OpenAI Math Release preprint
  (September 2026).
  [github.com/openai/math](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf)
-/

@[expose] public section

namespace Erdos181

open SimpleGraph

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and
$n2^{n-1}$ edges). Prove that $$R(Q_n) \ll 2^n.$$
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/cadamcat/hypercube-ramsey-lean4/blob/ad206e1bf8240c28b538dfe72f10364cbc1591da/HypercubeRamsey/Main.lean#L14"]
theorem erdos_181 :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n := by
  sorry

-- TODO: Add variants of the problem.

end Erdos181

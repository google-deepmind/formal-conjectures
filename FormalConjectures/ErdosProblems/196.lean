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
module

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Combinatorics.AP.Basic

/-!
# Erdős Problem 196

*References:*
- [erdosproblems.com/196](https://www.erdosproblems.com/196)
- [DEGS77] Davis, J. A. and Entringer, R. C. and Graham, R. L. and Simmons, G. J.,
  *On permutations containing no long arithmetic progressions*. Acta Arith. (1977), 81-90.
- [Ho26] Ho, Boon Suan, *A 4AP-free permutation of the positive integers*.
  [arXiv:2609.12780](https://arxiv.org/abs/2609.12780)
-/

@[expose] public section
namespace Erdos196

set_option linter.style.formal_proof_palomar false in
/--
Must every permutation of $\mathbb{N}$ contain a monotone 4-term arithmetic progression?

Here a monotone $k$-term arithmetic progression in a permutation $f$ is a set of indices
$i_1 < \cdots < i_k$ such that $f(i_1), \ldots, f(i_k)$ is an increasing or decreasing arithmetic
progression. [DEGS77] showed that every permutation of $\mathbb{N}$ contains a monotone 3-term
arithmetic progression, and that there are permutations with no monotone 5-term arithmetic
progression.

The answer is no: [Ho26] constructs an explicit permutation of the positive integers with no
monotone 4-term arithmetic progression. Independent constructions with Lean formalizations were
given shortly afterwards by Kruer and Kohlmeyer and, pseudonymously, in the repository
`coleski/erdos196`; the linked formal proof establishes the negation of this statement. -/
@[category research solved, question, AMS 5 11, formal_proof using lean4 at
  "https://github.com/lkruer/conjectures/blob/8ede860e8fc90a300207a2c17e8aefe6167b3086/problems/erdos-196/lean/Erdos196.lean"]
theorem erdos_196 : ¬ ∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4 := by
  sorry

end Erdos196

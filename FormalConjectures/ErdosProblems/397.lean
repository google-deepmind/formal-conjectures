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
# Erdős Problem 397

*References:*
- [erdosproblems.com/397](https://www.erdosproblems.com/397)
- [MathOverflow] (https://mathoverflow.net/questions/138209/product-of-central-binomial-coefficients)
-/

open Nat

namespace Erdos397

/--
Are there only finitely many solutions to
$$
  \prod_i \binom{2m_i}{m_i}=\prod_j \binom{2n_j}{n_j}
$$
with the $m_i,n_j$ distinct?

Somani, using ChatGPT, has given a negative answer. In fact, for any $a\geq 2$, if $c=8a^2+8a+1$,
$\binom{2a}{a}\binom{4a+4}{2a+2}\binom{2c}{c}= \binom{2a+2}{a+1}\binom{4a}{2a}\binom{2c+2}{c+1}.$
Further families of solutions are given in the comments by SharkyKesa.

This was earlier asked about in a [MathOverflow] question, in response to which Elkies also gave an
alternative construction which produces solutions - at the moment it is not clear whether Elkies'
argument gives infinitely many solutions (although Bloom believes that it can).
-/
@[category research solved, AMS 11]
theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
      ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  sorry

end Erdos397

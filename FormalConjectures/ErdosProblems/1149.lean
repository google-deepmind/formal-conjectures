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
public import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 1149

*References:*
- [erdosproblems.com/1149](https://www.erdosproblems.com/1149)
- [BeRi17] Bergelson, Vitaly and Richter, Florian Karl, *On the density of coprime tuples of the
  form $(n,\lfloor f_1(n)\rfloor,\dots,\lfloor f_k(n)\rfloor)$, where $f_1,\dots,f_k$ are
  functions from a Hardy field*. Number Theory - Diophantine Problems, Uniform Distribution and
  Applications, Springer (2017), 109-135. [arXiv:1611.08044](https://arxiv.org/abs/1611.08044)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

namespace Erdos1149

set_option linter.style.formal_proof_palomar false in
/--
Let $\alpha>0$ be a real number, not an integer. The density of integers $n\geq 1$ for which
$(n,\lfloor n^\alpha\rfloor)=1$ is $6/\pi^2$.

This is true, and was proved by Bergelson and Richter [BeRi17].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1149.lean#L136"]
theorem erdos_1149 (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2) := by
  sorry

end Erdos1149

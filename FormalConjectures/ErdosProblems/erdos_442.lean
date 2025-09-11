/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/442
import FormalConjectures.Util.ProblemImports
open scoped Topology

open Filter

noncomputable section

section Prelims

namespace Real

/--
The function $Log x := \max\{log x, 1\}$.
-/
def maxLogOne (x : ℝ) := max x.log 1

end Real

namespace Set

variable (A : Set ℕ) (x : ℝ)

local instance : Fintype <| ↑(A ∩ Set.Icc 1 ⌊x⌋₊) :=
  Set.finite_Icc 1 ⌊x⌋₊ |>.inter_of_right A |>.fintype

/--
If `A` is a set of natural numbers, then `A.bdd x` is the finite
set `{n ∈ A | n ≤ x}`.
-/
def bdd : Finset ℕ := (A ∩ Set.Icc 1 ⌊x⌋₊).toFinset

/--
If `A` be a set of natural numbers and let `x` be real, then
`A.bddProdUpper x` is the finite upper-triangular set of pairs
of elements of `A` that are `≤ x`. Specifically, it is the set
`{(n, m) | n ∈ A, n ≤ x, m ∈ A, m ≤ x, n < m}`
-/
def bddProdUpper : Finset (ℕ × ℕ) :=
  (A.bdd x ×ˢ A.bdd x).filter fun (n, m) => n < m

end Set

end Prelims

/--
Let $Log x := \max\{log x, 1\}$, $Log_2x = Log (Log x)$, and $Log_3x = Log (Log (Log x)))$.
Is it true that if $A\subseteq\mathbb{N}$ is such that
$$
\frac{1}{Log_2 x} \sum_{n\in A: n\leq x} \frac{1}{n}\to\infty
$$
then
$$
\left(\sum_{n\in A: n\leq x} \frac{1}{n}\right)^2 \sum_{n, m in A: n < m \leq x}
\frac{1}{\lcm(n, m)}\to\infty
$$
as $x\to\infty$?

Note: the informal and formal statements follow the solution paper
https://arxiv.org/pdf/2407.04226
-/
@[problem_status solved]
theorem erdos_442
    (A : Set ℕ)
    (hA : Tendsto (fun (x : ℝ) =>
      1 / x.maxLogOne.maxLogOne * ∑ n in A.bdd x, (1 : ℝ) / n) atTop atTop) :
    Tendsto (fun (x : ℝ) => 1 / (∑ n in A.bdd x, (1 : ℝ) / n) ^ 2 *
      ∑ nm in A.bddProdUpper x, (1 : ℝ) / nm.1.lcm nm.2) atTop atTop :=
  sorry

/--
Tao resolved erdos_442 in the negative in Theorem 1 of https://arxiv.org/pdf/2407.04226.
The following is a formalisation of that theorem with $C_0 = 1$.

Let $Log x := \max\{log x, 1\}$, $Log_2x = Log (Log x)$, and $Log_3x = Log (Log (Log x)))$.
There exists a set $A$ of natural numbers such that
$$
\sum_{n\in A: n\leq x} \frac{1}{n} =
  \exp\left(\left(\left(\frac{1}{2} + o(1)\right)Log_2^{1/2}x Log_3x\right)\right)
$$
and
$$
\sum_{n, m\in A: n, m\leq x} frac{1}{\lcm(n, m)}\ll\left(sum_{n\in A: n\leq x} \frac{1}{n}\right)^2
$$
-/
@[problem_status solved]
theorem erdos_442.variants.tao :
    ∃ (A : Set ℕ) (f : ℝ → ℝ) (C: ℝ) (hC : 0 < C) (hf : Tendsto f atTop (𝓝 0)),
      ∀ (x : ℝ),
        ∑ n in A.bdd x, (1 : ℝ) / n =
          Real.exp ((1 / 2 + f x) * √x.maxLogOne.maxLogOne * x.maxLogOne.maxLogOne.maxLogOne) ∧
        |∑ nm in A.bdd x ×ˢ A.bdd x, (1 : ℝ) / nm.1.lcm nm.2| ≤
          C * (∑ n in A.bdd x, (1 : ℝ) / n) ^ 2 :=
  sorry

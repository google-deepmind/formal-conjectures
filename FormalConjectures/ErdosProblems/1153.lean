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
# Erdős Problem 1153

*References:*
- [erdosproblems.com/1153](https://www.erdosproblems.com/1153)
- [ErTu61] Erdős, P. and Turán, P., *An extremal problem in the theory of interpolation*.
  Acta Math. Acad. Sci. Hungar. (1961), 221--234.
- [Ta26b] Tao, T., *Local Bernstein theory, and lower bounds for Lebesgue constants*.
  [arXiv:2603.21453](https://arxiv.org/abs/2603.21453) (2026).
- [Ya26] Yang, E., *A Lean formalisation of Erdős problem 1153* (2026).
  [GitHub](https://github.com/ethn-y/erdos-1153-lean).
-/

namespace Erdos1153

noncomputable section

/-- An injectively enumerated family of `n` distinct interpolation nodes in `[-1, 1]`. -/
structure NodeFamily (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_Icc : ∀ i, point i ∈ Set.Icc (-1 : ℝ) 1

/-- The `k`th Lagrange fundamental function. -/
def lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (x - nodes.point i) / (nodes.point k - nodes.point i)

/-- The Lebesgue function associated to a family of interpolation nodes. -/
def lebesgueFunction {n : ℕ} (nodes : NodeFamily n) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeFundamental nodes k x|

/--
For $x_1,\ldots,x_n\in [-1,1]$ let
$$
l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},
$$
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$. Let
$$
\lambda(x)=\sum_k \lvert l_k(x)\rvert.
$$
Is it true that, for any fixed $-1\leq a<b\leq 1$,
$$
\max_{x\in [a,b]}\lambda(x)>
\left(\frac{2}{\pi}-o(1)\right)\log n?
$$

This was resolved by Tao [Ta26b], who proved the stronger lower bound
$\max_{x\in[a,b]}\lambda(x)\geq \frac{2}{\pi}\log n-O(1)$.
-/
@[category research solved, AMS 41,
  formal_proof using lean4 at
    "https://github.com/ethn-y/erdos-1153-lean/blob/03bd3e064c0b95e8e7d335fa0f3e3de0713ca777/Erdos1153/Main.lean#L34"]
theorem erdos_1153 : answer(True) ↔
    ∀ a b : ℝ,
      -1 ≤ a → a < b → b ≤ 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
            ∃ x ∈ Set.Icc a b,
              (2 / Real.pi - ε) * Real.log (n : ℝ) < lebesgueFunction nodes x := by
  sorry

end

end Erdos1153

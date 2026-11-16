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
# Erdős Problem 824

*References:*
- [erdosproblems.com/824](https://www.erdosproblems.com/824)
- [Er59c] Erdős, P., *Remarks on number theory. II. Some problems on the $\sigma$ function*.
  Acta Arith. (1959), 171--177.
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974),
  197-202.
- [PoPo16] Pollack, Paul and Pomerance, Carl, *Some problems of Erdős on the sum-of-divisors
  function*. Trans. Amer. Math. Soc. Ser. B (2016), 1-26.
- [LiZh26] Li, Shisheng and Zhuang, Zhong, *Coprime pairs with equal sum of divisors, assuming
  smooth shifted primes*. Preprint (October 2026).
  [github.com/daizisheng/erdos-824](https://github.com/daizisheng/erdos-824/blob/b4b7099bb8ab9c1c7fc61dae18a73cdbe503fe5a/paper/erdos824.pdf)
- [OpenAI26] OpenAI, *Weighted dilation graphs, smooth shifted primes and totient fibers*.
  OpenAI Math Release preprint (September 2026).
  [github.com/openai/math](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
-/

@[expose] public section

open Filter
open scoped ArithmeticFunction.sigma

namespace Erdos824

/-- `h x` is the number of pairs of integers $1 \leq a < b < x$ such that $(a, b) = 1$ and
$\sigma(a) = \sigma(b)$, where $\sigma$ is the sum of divisors function.

We take $x$ to be a natural number. For real $x$ the count equals `h ⌈x⌉`, so the asymptotic
statements below do not change. -/
def h (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter fun (a, b) ↦
    a < b ∧ a.Coprime b ∧ σ 1 a = σ 1 b).card

/-- `hSquarefree x` is the number of pairs of integers $1 \leq a < b < x$ such that $a$ and $b$
are squarefree and $\sigma(a) = \sigma(b)$. -/
def hSquarefree (x : ℕ) : ℕ :=
  ((Finset.Ico 1 x ×ˢ Finset.Ico 1 x).filter fun (a, b) ↦
    a < b ∧ Squarefree a ∧ Squarefree b ∧ σ 1 a = σ 1 b).card

set_option linter.style.formal_proof_palomar false in
/--
Let $h(x)$ count the number of integers $1\leq a<b<x$ such that $(a,b)=1$ and
$\sigma(a)=\sigma(b)$, where $\sigma$ is the sum of divisors function. Is it true that
$h(x)>x^{2-o(1)}$?

That is, is it true that for every $\epsilon > 0$ we have $h(x) > x^{2-\epsilon}$ for all large
$x$? According to erdosproblems.com, Erdős [Er74b] proved that $\limsup h(x)/x = \infty$ and
claimed a similar proof for this problem.
-/
@[category research solved, question, AMS 11,
  formal_proof using lean4 at "https://github.com/cadamcat/equal-divisor-sums-lean4/blob/6280393739de142f3c54160ce7083110ed55f194/Erdos824/Theorem.lean#L17"]
theorem erdos_824 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (2 - ε) < (h x : ℝ) := by
  sorry

/--
Pollack and Pomerance [PoPo16, Section 6] proved that $h(x)/x \to \infty$, answering a question
of Erdős [Er59c].
-/
@[category research solved, AMS 11]
theorem erdos_824.variants.pollack_pomerance :
    Tendsto (fun x : ℕ ↦ (h x : ℝ) / (x : ℝ)) atTop atTop := by
  sorry

/--
A similar question can be asked if the condition $(a,b)=1$ is replaced by the condition that $a$
and $b$ are squarefree. Let $h'(x)$ count the number of squarefree integers $1\leq a<b<x$ with
$\sigma(a)=\sigma(b)$. Is it true that $h'(x)>x^{2-o(1)}$?
-/
@[category research open, question, AMS 11]
theorem erdos_824.variants.squarefree :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (2 - ε) < (hSquarefree x : ℝ) := by
  sorry

end Erdos824

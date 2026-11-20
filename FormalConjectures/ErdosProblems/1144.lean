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
# Erdős Problem 1144

*References:*
- [erdosproblems.com/1144](https://www.erdosproblems.com/1144)
- [520](https://www.erdosproblems.com/520)
- [At25] Atherfold, C., *Almost sure bounds for weighted sums of Rademacher random multiplicative
  functions*. [arXiv:2501.11076](https://arxiv.org/abs/2501.11076) (2025).
- [GoXu26] Gou, H. and Xu, M. W., *Large fluctuations of extended Rademacher random multiplicative
  functions*. [arXiv:2609.12940](https://arxiv.org/abs/2609.12940) (2026).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Real

namespace Erdos1144

/--
A function `f` : Z+ -> R is completely multiplicative if `f 1` = 1 and `f mn` = `f m` * `f n`
for all $m$ and $n$ > 0.
-/
def IsCompletelyMultiplicative (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n

/--
A random completely multiplicative function on a probability space $\Omega$:
for almost every $\omega$, `f \omega` is completely multiplicative, and for each prime $p$
we independently `f $p$` in {−1,1} uniformly at random.
-/
structure RandomMultiplicative {Ω : Type*} [MeasureSpace Ω]
    (f : Ω → ℕ → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure (volume : Measure Ω)
  completelyMultiplicative : ∀ᵐ ω ∂volume, IsCompletelyMultiplicative (f ω)
  measurable_prime : ∀ p : ℕ, p.Prime → Measurable (fun ω => f ω p)
  indep_primes : iIndepFun (fun (p : {p : ℕ // p.Prime}) ω => f ω p.1) volume
  rademacher_primes : ∀ p : ℕ, p.Prime →
    volume {ω | f ω p = 1} = ENNReal.ofReal (1 / 2) ∧
    volume {ω | f ω p = -1} = ENNReal.ofReal (1 / 2)

/--
Let `f` be a random completely multiplicative function, where for each prime $p$ we independently
choose `f $p$` in {−1,1} uniformly at random. Is it true that
$$\limsup_{N \to \infty} \frac{\sum_{m \leq N} f(m)}{\sqrt{N}} = \infty$$
with probability 1?

Gou and Xu [GoXu26] proved this holds almost surely in Theorem 1.1 using independent uniform prime
signs extended completely multiplicatively.
-/
@[category research solved, question, AMS 11 60]
theorem erdos_1144 {Ω : Type*} [MeasureSpace Ω] {f : Ω → ℕ → ℝ}
    (hf : RandomMultiplicative f) :
    ∀ᵐ ω ∂volume,
      limsup (fun N : ℕ => ((∑ m ∈ Finset.Icc 1 N, f ω m) / Real.sqrt N : EReal)) atTop = ⊤ := by
  sorry

/--
Atherfold [At25] proved that, almost surely,
$$\sum_{m \leq N} f(m) \ll N^{1/2} (\log N)^{1 + o(1)}.$$
Formulated here as: for every $\varepsilon > 0$, almost surely
$\sum_{m \leq N} f(m) = O(N^{1/2} (\log N)^{1 + \varepsilon})$ as $N \to \infty$.
-/
@[category research solved, AMS 11 60]
theorem erdos_1144.variants.atherfold {Ω : Type*} [MeasureSpace Ω] {f : Ω → ℕ → ℝ}
    (hf : RandomMultiplicative f) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂volume,
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N, f ω m) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log N) ^ (1 + ε)) := by
  sorry

end Erdos1144

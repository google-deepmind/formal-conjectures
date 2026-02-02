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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1144

*Reference:* [erdosproblems.com/1144](https://www.erdosproblems.com/1144)
-/

open MeasureTheory ProbabilityTheory Nat Real Filter

section Erdos1144

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/--
A random function $f$ is completely multiplicative if $f(1) = 1$,
for each prime $p$, we independently choose $f(p) \in \{-1, 1\}$ uniformly at random,
and for all positive integers $m, n$, $f(m \cdot n) = f(m) \cdot f(n)$.
-/
structure IsRandomCompletelyMultiplicative (f : ℕ → Ω → ℝ) : Prop where
  /-- Prime entries are independent. -/
  iIndepFun_primes : iIndepFun (fun p : Primes ↦ f p) ℙ
  /-- Prime entries are uniformly distributed on `{-1, 1}`. -/
  prob_of_prime p : p.Prime → ℙ {ω | f p ω = 1} = 1 / 2 ∧ ℙ {ω | f p ω = -1} = 1 / 2
  /-- $f(1) = 1$. -/
  map_one ω : f 1 ω = 1
  /-- $f(m \cdot n) = f(m) \cdot f(n)$ for all positive integers $m$, $n$. -/
  map_mul m n ω : f (m * n) ω = f m ω * f n ω

/--
Let $f$ be a random completely multiplicative function on the positive integers,
where for each prime $p$, we independently choose $f(p) \in \{-1, 1\}$ with equal probability.
Is it true that, almost surely,
\[
  \limsup_{N \to \infty} \frac{\sum_{m \leq N} f(m)}{\sqrt{N}} = \infty?
\]
-/
@[category research open, AMS 11 60]
theorem erdos_1144 :
    answer(sorry) ↔ ∀ (f : ℕ → Ω → ℝ), IsRandomCompletelyMultiplicative f →
      ∀ᵐ ω, Filter.atTop.limsup
        (fun N => ((∑ m ∈ Finset.Icc 1 N, f m ω) / Real.sqrt N).toEReal) = ⊤ := by
  sorry

end Erdos1144

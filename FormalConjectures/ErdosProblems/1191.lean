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
# Erdős Problem 1191

*References:*
- [erdosproblems.com/1191](https://www.erdosproblems.com/1191)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [HaRo66] Halberstam, H. and Roth, K. F., *Sequences. Vol. I*. (1966), xx+291.
-/

@[expose] public section

open Filter Real

namespace Erdos1191

/--
Let $A\subset\mathbb{N}$ be an infinite Sidon set. Is it true that
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}=0?$$

Here $x$ runs over $\mathbb{N}$ and the $\liminf$ is taken in `ℝ≥0∞`, so that it is $\infty$
rather than $0$ when the sequence tends to infinity.
-/
@[category research open, question, AMS 5 11]
theorem erdos_1191.parts.i : ∀ A : Set ℕ, A.Infinite → IsSidon A →
    liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0 := by
  sorry

/--
Does there exist an infinite Sidon set $A$ such that
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^c>0$$
for some $c>0$?

A positive answer would also give a positive answer to Erdős Problem 39.
-/
@[category research open, question, AMS 5 11]
theorem erdos_1191.parts.ii : ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
    ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ c)) atTop := by
  sorry

/--
Erdős proved (see for example [HaRo66]) that if $A$ is an infinite Sidon set then
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}\leq c$$
for some constant $c>0$. See also `erdos_158.variants.isSidon'`.
-/
@[category research solved, AMS 5 11]
theorem erdos_1191.variants.liminf_le {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  sorry

end Erdos1191

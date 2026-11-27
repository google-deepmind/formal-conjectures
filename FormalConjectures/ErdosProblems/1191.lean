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
- [Er55] Stöhr, Alfred, *Gelöste und ungelöste Fragen über Basen der natürlichen Zahlenreihe. II*.
  J. Reine Angew. Math. 194 (1955), 111-140.
- [ErRe60] Erdős, P. and Rényi, A., *Additive properties of random sequences of positive integers*.
  Acta Arith. 6 (1960), 83-110.
- [HaRo66] Halberstam, H. and Roth, K. F., *Sequences. Vol. I*. (1966), xx+291.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
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
An affirmative answer to `erdos_1191.parts.i` immediately rules out the $c = 1/2$ case of
`erdos_1191.parts.ii`.
-/
@[category API, AMS 5 11]
theorem erdos_1191.variants.parts_i_implies_not_parts_ii_half
    (h : ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0) :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop := by
  rintro ⟨A, hAinf, hAsid, hpos⟩
  rw [h A hAinf hAsid] at hpos
  exact lt_irrefl 0 hpos

/--
Erdős proved (see for example [Er55] and [HaRo66]) that if $A$ is an infinite Sidon set then
$$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}\leq c$$
for some constant $c>0$. See also `erdos_158.variants.isSidon'`.
-/
@[category research solved, AMS 5 11]
theorem erdos_1191.variants.liminf_le {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  sorry

/--
An affirmative answer to `erdos_1191.parts.i` immediately implies `erdos_1191.variants.liminf_le`
with any $c > 0$.
-/
@[category API, AMS 5 11]
theorem erdos_1191.variants.parts_i_implies_liminf_le
    (h : ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (fun x : ℕ ↦ ENNReal.ofReal
        ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop = 0)
    {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    ∃ c > (0 : ℝ), liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * log x ^ (1 / 2 : ℝ))) atTop ≤
        ENNReal.ofReal c := by
  refine ⟨1, zero_lt_one, ?_⟩
  rw [h A hAinf hAsid]
  exact zero_le

end Erdos1191

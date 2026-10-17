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
# Erdős Problem 1122

*References:*
- [erdosproblems.com/1122](https://www.erdosproblems.com/1122)
- [Er46] Erdős, P., *On the distribution function of additive functions*. Annals of Math. (1946),
  1-20.
- [Ma22] Mangerel, Alexander P., *Additive functions in short intervals, gaps and a conjecture of
  Erdős*. Ramanujan J. (2022), 1023--1090.
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos1122

/--
Let $f:\mathbb{N}\to \mathbb{R}$ be an additive function (i.e. $f(ab)=f(a)+f(b)$ whenever
$(a,b)=1$). Let
$$A=\{ n \geq 1: f(n+1)< f(n)\}.$$
If $\lvert A\cap [1,X]\rvert =o(X)$ then must $f(n)=c\log n$ for some $c\in \mathbb{R}$?

The condition $\lvert A\cap [1,X]\rvert =o(X)$ says that $A$ has natural density $0$.

Partial progress was made by Mangerel [Ma22], who proved that this is true for completely
additive $f$ if
$$\lvert A\cap [1,X]\rvert \ll \frac{X}{(\log X)^{2+c}}$$
for some $c>0$, and if $f(p)$ does not have very large values (in a certain technical sense).

See also `erdos_491`.
-/
@[category research open, AMS 11]
theorem erdos_1122 : answer(sorry) ↔ ∀ f : ℕ → ℝ,
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    {n | 1 ≤ n ∧ f (n + 1) < f n}.HasDensity 0 →
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

/--
Erdős [Er46] proved that $f(n)=c\log n$ for some $c\in\mathbb{R}$ if $A$ is empty, that is, if
$f(n) \leq f(n+1)$ for all $n \geq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_1122.variants.monotone (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

/--
Erdős [Er46] proved that $f(n)=c\log n$ for some $c\in\mathbb{R}$ if $f(n+1)-f(n)=o(1)$.
-/
@[category research solved, AMS 11]
theorem erdos_1122.variants.sub_tendsto_zero (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hdiff : Tendsto (fun n ↦ f (n + 1) - f n) atTop (𝓝 0)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

/--
For $c \geq 0$ the function $c \log n$ is additive and $A$ is empty, so it satisfies the
hypotheses of `erdos_1122`.
-/
@[category test, AMS 11]
theorem const_mul_log (c : ℝ) (hc : 0 ≤ c) (f : ℕ → ℝ) (hf : ∀ n, f n = c * Real.log n) :
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) ∧
      {n | 1 ≤ n ∧ f (n + 1) < f n}.HasDensity 0 := by
  refine ⟨fun a ha b hb _ ↦ ?_, ?_⟩
  · simp only [hf, Nat.cast_mul]
    rw [Real.log_mul (by positivity) (by positivity), mul_add]
  · convert Set.HasDensity.empty
    refine Set.eq_empty_of_forall_notMem fun n ⟨hn, hlt⟩ ↦ hlt.not_ge ?_
    simp only [hf]
    gcongr
    simp

end Erdos1122

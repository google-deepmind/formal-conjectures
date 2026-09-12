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
# Erdős Problem 1122

*References:*
- [erdosproblems.com/1122](https://www.erdosproblems.com/1122)
- [Er46] Erdős, P., *On the distribution function of additive functions*. Ann. of Math. (2)
  (1946), 1--20.
- [Ma22] Mangerel, Alexander P., *Additive functions in short intervals, gaps and a conjecture
  of Erdős*. Ramanujan J. (2022), 1023--1090.
-/

open Filter Set Asymptotics

namespace Erdos1122

/--
Let $f:\mathbb{N}\to \mathbb{R}$ be an additive function (i.e. $f(ab)=f(a)+f(b)$ whenever
$(a,b)=1$). Let
$$A=\{ n \geq 1: f(n+1)< f(n)\}.$$
If $\lvert A\cap [1,X]\rvert =o(X)$ then must $f(n)=c\log n$ for some $c\in \mathbb{R}$?

Erdős proved that $f(n)=c\log n$ for some $c\in\mathbb{R}$ if $A$ is empty, or if
$f(n+1)-f(n)=o(1)$.

Partial progress was made by Mangerel [Ma22], who proved that this is true if
$$\lvert A\cap [1,X]\rvert \ll \frac{X}{(\log X)^{2+c}}$$
for some $c>0$, and if $f(p)$ does not have very large values (in a certain technical sense).

See also [erdosproblems.com/491](https://www.erdosproblems.com/491).
-/
@[category research open, AMS 11]
theorem erdos_1122 : answer(sorry) ↔ ∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((fun X : ℕ ↦ (({n | 1 ≤ n ∧ f (n + 1) < f n} ∩ Icc 1 X).ncard : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ))) →
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

end Erdos1122

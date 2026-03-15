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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 1122

If $f : \mathbb{N} \to \mathbb{R}$ is an additive function such that the set
$\{n : f(n+1) < f(n)\}$ has natural density zero, then $f(n) = c \cdot \log(n)$
for some constant $c$.

*Reference:* [erdosproblems.com/1122](https://www.erdosproblems.com/1122)

See also Erdős Problem 491 for the stronger hypothesis $|f(n+1) - f(n)| < c$.

[Er46] Erdős, P., _On the distribution function of additive functions_, Ann. of Math. (2) 47
(1946), 1-20.

[Ma22] Mangerel, A. P., _Additive functions in short intervals, gaps and a conjecture of Erdős_.
Ramanujan J. (2022), 1023-1090.
-/

namespace Erdos1122

/--
Let $f : \mathbb{N} \to \mathbb{R}$ be an additive function (i.e., $f(ab) = f(a) + f(b)$ whenever
$\gcd(a,b) = 1$). Let $A = \{n \geq 1 : f(n+1) < f(n)\}$.
If $|A \cap [1,X]| = o(X)$ (the set $A$ has natural density zero), then
$f(n) = c \cdot \log(n)$ for some $c \in \mathbb{R}$.

Erdős proved that $f(n) = c \cdot \log(n)$ if $A$ is empty, or if $f(n+1) - f(n) = o(1)$ [Er46].
Partial progress was made by Mangerel [Ma22], who proved this under the stronger bound
$|A \cap [1,X]| \ll X / (\log X)^{2+c}$ for some $c > 0$, with restrictions on the values of
$g(p)$.
-/
@[category research open, AMS 11]
theorem erdos_1122
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hA : Set.HasDensity {n : ℕ | f (n + 1) < f n} 0) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) := by
  sorry

end Erdos1122

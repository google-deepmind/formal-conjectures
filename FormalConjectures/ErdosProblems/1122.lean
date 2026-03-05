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
# Erdős Problem 1122

If $f : \mathbb{N} \to \mathbb{R}$ is an additive function such that the set
$\{n : f(n+1) < f(n)\}$ has natural density zero, then $f(n) = c \cdot \log(n)$
for some constant $c$.

*Reference:* [erdosproblems.com/1122](https://www.erdosproblems.com/1122)

[Er46] Erdős, P., _On the distribution function of additive functions_, Ann. of Math. (2) 47
(1946), 1-20.

[Ma22] Mangerel, A. P., _On additive functions with small increments_, 2022.
-/

namespace Erdos1122

/--
Let $f : \mathbb{N} \to \mathbb{R}$ be an additive function (i.e., $f(ab) = f(a) + f(b)$ whenever
$\gcd(a,b) = 1$). Let $A = \{n \geq 1 : f(n+1) < f(n)\}$.
If $|A \cap [1,X]| = o(X)$ (the set $A$ has natural density zero), then
$f(n) = c \cdot \log(n)$ for some $c \in \mathbb{R}$.

Erdős proved that $f(n) = c \cdot \log(n)$ if $A$ is empty, or if $f(n+1) - f(n) = o(1)$ [Er46].
Partial progress was made by Mangerel [Ma22].
-/
@[category research open, AMS 11]
theorem erdos_1122
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hA : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ X : ℕ, X ≥ N →
      (((Finset.Icc 1 X).filter (fun n => f (n + 1) < f n)).card : ℝ) ≤ ε * (X : ℝ)) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) := by
  sorry

end Erdos1122

/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 477

*Reference:* [erdosproblems.com/477](https://www.erdosproblems.com/477)
-/

open Polynomial Set

namespace Erdos477

/--
Let $f = X ^ 2$ be a polynomial of degree at least $2$. Then there is not set
$A$ such that every $z\in \mathbb{Z}$ has exactly one representation as
$z=a+f(n)$ for some $a\in A$ and $n > 0$
-/
@[category research solved, AMS 12]
theorem erdos_477.variants.explicit_counterexample :
    letI f := X ^ 2
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

/--
There is no such $A$ for any polynomial $f(x) = aX^2 + bX + c$, if $a | b$
with $a \ne 0$ and $b \ne 0.
This was found be AlphaProof for the specific instance $X^2 - X + 1$ and then generalised.
 -/
@[category research solved, AMS 12]
theorem erdos_477.variants.strong_negation_degree_two_dvd_condition_b_ne_zero (a b c : ℤ) :
    let f := a • X ^ 2 + b • X + C c
    a ≠ 0 → b ≠ 0 → a ∣ b →
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry


/--
Probably there is no such $A$ for any polynomial $f$ of degree $2$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_degree_eq_two (f : Polynomial ℤ) (hf₀ : 2 = f.degree) :
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry


/--
Probably there is no such $A$ for the polynomial $X^3$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_pow_three :
    letI f := X ^ 3
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

/--
Probably there is no such $A$ for the polynomial $X^k$ for any $k \ge 0$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_monomial (k : ℕ) (hk : 2 ≤ k):
    letI f := X ^ k
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

/--
Let $f:\mathbb{Z}\to \mathbb{Z}$ be a polynomial of degree at least $2$. Is there a set $A$ such
that every $z\in \mathbb{Z}$ has exactly one representation as $z=a+f(n)$ for some $a\in A$ and
$n > 0$?
-/
@[category research solved, AMS 12]
theorem erdos_477 : answer(False) ↔ ∀ (f : Polynomial ℤ), 2 ≤ f.degree →
    (∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2) := by
  simp only [false_iff, not_forall]
  exact ⟨.X ^ 2, by simp, erdos_477.variants.explicit_counterexample⟩

/--
Probably there is no such $A$ for any polynomial $f$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation (f : Polynomial ℤ) (hf₀ : 2 ≤ f.degree) :
    ¬ ∃ A : Set ℤ, ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

end Erdos477

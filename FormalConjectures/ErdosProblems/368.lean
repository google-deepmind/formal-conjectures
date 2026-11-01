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
# Erdős Problem 368

*References:*
- [erdosproblems.com/368](https://www.erdosproblems.com/368)
- [Er76d] Erdős, P., Problems and results on number theoretic properties of consecutive
  integers and related questions. Proceedings of the Fifth Manitoba Conference on Numerical
  Mathematics (1976), 25–44.
- [Po18] Pólya, Georg, Zur arithmetischen Untersuchung der Polynome.
  Math. Z. (1918), 143–148.
- [Sc67b] Schinzel, A., On two theorems of Gelfond and some of their applications.
  Acta Arith. (1967/68), 177–236.
-/

@[expose] public section

namespace Erdos368

open Filter

/-- The largest prime factor of $n(n+1)$. -/
def F (n : ℕ) : ℕ := (n * (n + 1)).maxPrimeFac

/--
How large is the largest prime factor of $n(n+1)$?
The truth is probably $F(n)\gg (\log n)^2$ for all $n$.
-/
@[category research open, AMS 11]
theorem erdos_368.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.log n ^ 2 ≤ (F n : ℝ) := by
  sorry

/--
Erdős [Er76d] conjectured that, for every $\epsilon>0$, there are infinitely many $n$
such that $F(n)<(\log n)^{2+\epsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_368.upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, (F n : ℝ) < Real.log n ^ (2 + ε) := by
  sorry

/-- Pólya [Po18] proved that $F(n)\to\infty$ as $n\to\infty$. -/
@[category research solved, AMS 11]
theorem erdos_368.variants.tendsto : Tendsto F atTop atTop := by
  sorry

/--
For every $\delta>0$, there are infinitely many $n$ with $F(n)\leq n^\delta$.
This follows from Schinzel's [Sc67b] observation that, for infinitely many $n$,
$F(n)\leq n^{O(1/\log\log\log n)}$.
-/
@[category research solved, AMS 11]
theorem erdos_368.variants.subpower :
    ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop, (F n : ℝ) ≤ (n : ℝ) ^ δ := by
  sorry

@[category test, AMS 11]
example : F 1 = 2 := by decide +kernel

@[category test, AMS 11]
example : F 8 = 3 := by decide +kernel

@[category test, AMS 11]
example : F 80 = 5 := by decide +kernel

@[category test, AMS 11]
example : F 4374 = 7 := by decide +kernel

end Erdos368

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
# Erdős Problem 945

*References:*
 - [erdosproblems.com/945](https://www.erdosproblems.com/945)
 - [ErMi52] Erdős, P. and Mirsky, L., The distribution of values of the divisor function {$d(n)$}. Proc. London Math. Soc. (3) (1952), 257--271.
-/

open Filter Real


private abbrev τ  := fun (n : ℕ) => n.divisors.card

private noncomputable def F (x : ℝ) : ℕ :=
  sSup {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

/--
Is it true that $F(x) \leq (\log x)^{O(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_945 : (∃ (O : ℝ → ℝ), O =O[Filter.atTop] (1 : ℝ → ℝ) ∧ ∀ (x : ℝ),
    F x ≤ x.log ^ (O x)) ↔ answer(sorry) := by
  sorry

/--
Is there a constant $C > 0$ such that, for all large $x$, every interval $[x, x+(\log x)C]$
contains two integers with the same number of divisors?
-/
@[category research open, AMS 11]
theorem erdos_945.variants.constant : (∃ (C : ℝ), C > 0 ∧ ∃ x₀, ∀ (x : ℝ), x₀ < x →
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + (x.log)^C) ∧
    ↑b ∈ Set.Icc x (x + (x.log)^C) ∧
    τ a = τ b) ↔ answer(sorry) := by
  sorry

-- TODO(firsching): show equivalence
/--
The two ways of phrasing the conjecture are equivalent.
-/
@[category undergraduate, AMS 11]
theorem erdos_945.equivalence :
    (∃ (O : ℝ → ℝ), O =O[atTop] (1 : ℝ → ℝ) ∧ ∀ (x : ℝ),
    F x ≤ x.log ^ (O x)) ↔
    (∃ (C : ℝ), C > 0 ∧ ∃ x₀, ∀ (x : ℝ), x₀ < x →
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + (x.log)^C) ∧
    ↑b ∈ Set.Icc x (x + (x.log)^C) ∧
    τ a = τ b) := by
  sorry


/--
Erdős and Mirsky [ErMi52] proved that $\frac{(\log x)^{1/2}}{\log\log x}\ll F(x)$.
-/
@[category research solved, AMS 11]
theorem erdos_945.variants.lower_bound :
    (fun (x : ℕ) => (log x).sqrt /(log x).log) =O[atTop] fun (n : ℕ) => (F n : ℝ) := by
  sorry

/--
Erdős and Mirsky [ErMi52] proved that $\log F(x) <<  \frac{(\log x)^{1/2}}$.
-/
@[category research solved, AMS 11]
theorem erdos_945.variants.upper_bound :
    (fun (n : ℕ) => (F n : ℝ).log) =O[atTop] fun (x : ℕ) => (log x).sqrt /(log x).log := by
  sorry


-- TODO(firsching): add observations what follows from Cramér's conjecture and if every sufficient
-- interval contains a squarefree number.

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
# Erdős Problem 462

Is it true that there exists a constant $C > 0$ such that the sum of $p(n)/n$
over composite $n$ in $[x, x + C\sqrt{x}(\log x)^2]$ is $\gg 1$ for all
large $x$? Here $p(n)$ denotes the least prime factor of $n$.

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p. 92.
-/

open Finset Filter Real

open scoped BigOperators

namespace Erdos462

/--
Erdős Problem 462 [ErGr80, p.92]:

Is it true that there exists a constant $C > 0$ such that the sum of $p(n)/n$
over composite $n$ in $[x, x + C\sqrt{x}(\log x)^2]$ is $\gg 1$ for all
large $x$? Here $p(n)$ denotes the least prime factor of $n$.
-/
@[category research open, AMS 11]
theorem erdos_462 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ δ : ℝ, δ > 0 ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      δ ≤ ∑ n ∈ (Finset.Icc x
        (x + ⌊C * Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2⌋₊)).filter
        (fun n => ¬ Nat.Prime n),
        (Nat.minFac n : ℝ) / (n : ℝ) := by
  sorry

/--
Erdős Problem 462 (Background asymptotic) [ErGr80, p.92]:

There exists a constant $c > 0$ such that the sum of $p(n)/n$ over composite
$n \leq x$ is asymptotic to $c \cdot \sqrt{x} / (\log x)^2$, where $p(n)$
denotes the least prime factor of $n$.
-/
@[category research solved, AMS 11]
theorem erdos_462.variants.asymptotic :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun x : ℕ =>
        (∑ n ∈ (Finset.Icc 2 x).filter (fun n => ¬ Nat.Prime n),
          (Nat.minFac n : ℝ) / (n : ℝ)) /
        (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ 2))
        atTop (nhds c) := by
  sorry

end Erdos462

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
# Erdős Problem 994

Khintchine's conjecture on strong uniform distribution: is it true that for almost all real
numbers α, the fractional parts {kα} are equidistributed with respect to every measurable subset
of (0,1)? Disproved by Marstrand [Ma70].

*Reference:* [erdosproblems.com/994](https://www.erdosproblems.com/994)

[Er64b] Erdős, P., _Problems and results on diophantine approximations_.
Compositio Math. (1964), 52–65.

[Kh23] Khintchine, A., _Ein Satz über Kettenbrüche, mit arithmetischen Anwendungen_.
Math. Z. **18** (1923), 289–306.

[Ma70] Marstrand, J. M., _On Khintchine's conjecture about strong uniform distribution_.
Proc. London Math. Soc. (3) **21** (1970), 540–556.
-/

open scoped MeasureTheory

open Filter Finset Set MeasureTheory

namespace Erdos994

/-- The Cesàro frequency of visits of the fractional parts $\{k\alpha\}$ to a set $E$,
for $k = 1, \ldots, n$. That is, $\frac{1}{n} \cdot \#\{1 \le k \le n : \{k\alpha\} \in E\}$. -/
noncomputable def cesaroFrequency (α : ℝ) (E : Set ℝ) (n : ℕ) : ℝ :=
  have : DecidablePred (· ∈ E) := Classical.decPred _
  ((Finset.range n).filter (fun (k : ℕ) =>
    Int.fract (((k : ℝ) + 1) * α) ∈ E)).card / (n : ℝ)

/--
Erdős Problem 994 (Khintchine's conjecture, disproved by Marstrand [Ma70]):

Let $E \subseteq (0,1)$ be a measurable subset with Lebesgue measure $\lambda(E)$. Is it true
that, for almost all $\alpha$,
$$
  \lim_{n \to \infty} \frac{1}{n} \sum_{1 \le k \le n} \mathbf{1}_{\{\{k\alpha\} \in E\}} = \lambda(E)
$$
for all $E$?

This is false, and was disproved by Marstrand [Ma70].
-/
@[category research solved, AMS 11 28]
theorem erdos_994 : answer(False) ↔
    ∀ᵐ α ∂(volume : Measure ℝ),
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Ioo 0 1 →
        Tendsto (cesaroFrequency α E) atTop
          (nhds (volume E).toReal) := by
  sorry

end Erdos994

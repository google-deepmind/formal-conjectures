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
# Erdős Problem 270

*Reference:* [erdosproblems.com/270](https://www.erdosproblems.com/270)

Let $f(n) \to \infty$. Is it true that $\sum 1/(n+1)\cdots(n+f(n))$ is irrational?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p.66.

[CrKo25] Crmarić and Kovač, disproof of the conjecture.
-/

open Filter Finset BigOperators

namespace Erdos270

/--
Erdős Problem 270 [ErGr80, p.66] (Disproved):

Let $f(n) \to \infty$ as $n \to \infty$. Is it true that
$$\sum_{n \geq 1} \frac{1}{(n+1)\cdots(n+f(n))}$$
is irrational?

Disproved by Crmarić and Kovač [CrKo25].
-/
@[category research solved, AMS 11 40]
theorem erdos_270 : answer(False) ↔
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      Irrational (∑' n, (1 : ℝ) / ∏ i ∈ Finset.range (f (n + 1)),
        ((n : ℝ) + 2 + (i : ℝ))) := by
  sorry

/--
Stronger result from Crmarić and Kovač [CrKo25]: for any $\alpha > 0$ there exists
$f : \mathbb{N} \to \mathbb{N}$ with $f(n) \to \infty$ such that the sum equals $\alpha$.
-/
@[category research solved, AMS 11 40]
theorem erdos_270.variants.stronger_disproof :
    ∀ α : ℝ, 0 < α →
      ∃ f : ℕ → ℕ,
        Tendsto f atTop atTop ∧
        HasSum (fun n => (1 : ℝ) / (∏ i ∈ Finset.range (f (n + 1)),
          ((n : ℝ) + 2 + (i : ℝ)))) α := by
  sorry

end Erdos270

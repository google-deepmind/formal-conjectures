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
# Erdős Problem 50

*Reference:* [erdosproblems.com/50](https://www.erdosproblems.com/50)

The distribution function $f(c) = d(\{n : \varphi(n) < cn\})$ is purely singular: there is
no $x$ at which $f'(x)$ exists and is positive. Proved by Erdős.
-/

open Nat Finset Filter Set Classical

namespace Erdos50

/-- Count of natural numbers $n$ in $\{1, \ldots, N\}$ with $\varphi(n) < c \cdot n$. -/
noncomputable def totientDensityCount (c : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => 0 < n ∧ (Nat.totient n : ℝ) < c * ↑n)).card

/--
Schoenberg proved that for every $c \in [0,1]$ the natural density of
$\{n \in \mathbb{N} : \varphi(n) < cn\}$ exists. Let this density be denoted by $f(c)$.
Is it true that there are no $x$ such that $f'(x)$ exists and is positive?

Erdős proved the distribution function $f$ is purely singular.
-/
@[category research solved, AMS 11 26]
theorem erdos_50 : answer(True) ↔
    ∀ f : ℝ → ℝ,
      (∀ c ∈ Icc (0 : ℝ) 1,
        Tendsto (fun N : ℕ => (totientDensityCount c N : ℝ) / ↑N) atTop (nhds (f c))) →
      ∀ x d : ℝ, HasDerivAt f d x → d ≤ 0 := by
  sorry

end Erdos50

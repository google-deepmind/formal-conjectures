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
# Erdős Problem 1184

*Reference:* [erdosproblems.com/1184](https://www.erdosproblems.com/1184)
-/

open Filter Finset Real
open scoped Topology

namespace Erdos1184

/-- $f(n,k)$ counts the number of $1\leq i\leq k$ such that $P(n+i)>k$, where $P(m)$ is the
largest prime divisor of $m$. -/
noncomputable def f (n k : ℕ) : ℕ :=
  { i ∈ Icc 1 k | k < (n + i).maxPrimeFac }.card

/--
Let $f(n,k)$ count the number of $1\leq i\leq k$ such that $P(n+i)>k$ (where $P(m)$ is the largest
prime divisor of $m$). Is it true that, if $\alpha>1$ is such that $n=k^{\alpha+o(1)}$, then
$$
f(n,k)=(1-\rho(\alpha)+o(1))k,
$$
where $\rho$ is the Dickman function?
-/
@[category research open, AMS 11]
theorem erdos_1184 :
    answer(sorry) ↔
      ∃ ρ : ℝ → ℝ, ∀ α > (1 : ℝ),
        ∀ n k : ℕ → ℕ,
          Tendsto (fun t : ℕ ↦ log (n t) / log (k t)) atTop (𝓝 α) →
            Tendsto (fun t : ℕ ↦ (Erdos1184.f (n t) (k t) : ℝ) / k t)
              atTop (𝓝 (1 - ρ α)) := by
  sorry

end Erdos1184

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
# Erdős Problem 1001

*Reference:* [erdosproblems.com/1001](https://www.erdosproblems.com/1001)
-/

open Filter MeasureTheory Set Real
open scoped Topology

namespace Erdos1001

/-- The set of $\alpha\in(0,1)$ such that $|\alpha-x/y|<A/y^2$ for some coprime $x,y$ with
$N\leq y\leq cN$. -/
def S_set (N : ℕ) (A c : ℝ) : Set ℝ :=
  { α ∈ Ioo (0 : ℝ) 1 | ∃ x y : ℕ, N ≤ y ∧ (y : ℝ) ≤ c * N ∧ Nat.Coprime x y ∧
      |α - (x : ℝ) / y| < A / y ^ 2 }

noncomputable def S (N : ℕ) (A c : ℝ) : ℝ := (volume (S_set N A c)).toReal

/--
Let $S(N,A,c)$ be the measure of the set of those $\alpha\in (0,1)$ such that
$$
\left\lvert \alpha-\frac{x}{y}\right\rvert< \frac{A}{y^2}
$$
for some $N\leq y\leq cN$ and $(x,y)=1$. Does
$$
\lim_{N\to \infty}S(N,A,c)=f(A,c)
$$
exist? What is its explicit form?
-/
@[category research open, AMS 11]
theorem erdos_1001 :
    answer(sorry) ↔
      ∀ A > (0 : ℝ), ∀ c > (1 : ℝ),
        ∃ f : ℝ, Tendsto (fun N : ℕ ↦ S N A c) atTop (𝓝 f) := by
  sorry

end Erdos1001

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
# Erdős Problem 29

*Reference:* [erdosproblems.com/29](https://www.erdosproblems.com/29)

There exists a set $A \subseteq \mathbb{N}$ that is an additive basis of order 2 (i.e.,
$A + A = \mathbb{N}$) whose representation function grows sub-polynomially: $r_A(n) = o(n^\varepsilon)$
for every $\varepsilon > 0$. First proved by Erdős via probabilistic methods; an explicit
construction was given by Jain, Pham, Sawhney, and Zakharov (2024).
-/

open Filter Asymptotics Classical

namespace Erdos29

/--
The additive representation function $r_A(n) = (1_A * 1_A)(n)$ counts the number of ordered
pairs $(a, b)$ with $a, b \in A$ and $a + b = n$. This is the Dirichlet convolution of the
indicator function $1_A$ with itself, evaluated at $n$.
-/
noncomputable def addRepFun (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

/--
There exists a set $A \subseteq \mathbb{N}$ such that:
1. $A$ is an additive basis of order 2: every natural number is a sum of two elements of $A$
   (i.e., $A + A = \mathbb{N}$), and
2. The additive representation function $r_A(n) = (1_A * 1_A)(n)$ grows sub-polynomially:
   $r_A(n) = o(n^\varepsilon)$ for every $\varepsilon > 0$.

The existence of such a set was first proved by Erdős using probabilistic methods
(answering a question of Sidon from 1932). An explicit construction was given by
Jain, Pham, Sawhney, and Zakharov (2024).
-/
@[category research solved, AMS 5 11]
theorem erdos_29 :
    answer(True) ↔
    ∃ A : Set ℕ,
      (∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ => (addRepFun A n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ε) := by
  sorry

end Erdos29

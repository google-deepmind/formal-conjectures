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
# Erdős Problem 793

*Reference:* [erdosproblems.com/793](https://www.erdosproblems.com/793)

Let $F(n)$ be the maximum possible size of a subset $A \subseteq \{1, \ldots, n\}$ such that
$a \nmid bc$ whenever $a, b, c \in A$ with $a \neq b$ and $a \neq c$. Is there a constant $C$
such that
$$
  F(n) = \pi(n) + (C + o(1)) \cdot n^{2/3} \cdot (\log n)^{-2}?
$$

Erdős [Er38] proved there exist constants $0 < c_1 \leq c_2$ such that
$$
  \pi(n) + c_1 \cdot n^{2/3} \cdot (\log n)^{-2} \leq F(n)
    \leq \pi(n) + c_2 \cdot n^{2/3} \cdot (\log n)^{-2}.
$$

See also problem #425.
-/

open Filter

open scoped Topology Real

namespace Erdos793

/--
A finite set $A \subseteq \mathbb{N}$ is *primitive-like* if no element divides
the product of two other elements: for all $a, b, c \in A$ with $a \neq b$ and $a \neq c$,
$a \nmid bc$.
-/
def IsPrimitiveLike (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → ¬(a ∣ b * c)

/--
$F(n)$ is the maximum cardinality of a primitive-like subset of $\{1, \ldots, n\}$.
-/
noncomputable def primitiveLikeMaxSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, IsPrimitiveLike A ∧ (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) ∧ A.card = k}

/--
Erdős Problem 793 [Er69][Er70b]:

Is there a constant $C > 0$ such that
$$
  \frac{F(n) - \pi(n)}{n^{2/3} / (\log n)^2} \to C?
$$
-/
@[category research open, AMS 5 11]
theorem erdos_793 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
      Tendsto
        (fun n : ℕ =>
          ((primitiveLikeMaxSize n : ℝ) - (Nat.primeCounting n : ℝ)) /
          ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log (n : ℝ)) ^ (2 : ℝ)))
        atTop
        (nhds c) := by
  sorry

end Erdos793

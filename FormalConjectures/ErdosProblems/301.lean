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
# Erdős Problem 301

*References:*
- [erdosproblems.com/301](https://www.erdosproblems.com/301)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980), 39.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Erdos301

/--
A finite set $A$ of positive integers admits no solution to
$\frac{1}{a} = \frac{1}{b_1} + \cdots + \frac{1}{b_k}$ with $a \in A$ and a nonempty subset
$B = \{b_1, \ldots, b_k\} \subseteq A \setminus \{a\}$.
-/
def NoUnitFractionSum (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ B ⊆ A.erase a, B.Nonempty →
    (1 : ℚ) / a ≠ ∑ b ∈ B, (1 : ℚ) / b

/--
$f(N)$ is the size of the largest $A \subseteq \{1, \ldots, N\}$ containing no solution to
$\frac{1}{a} = \frac{1}{b_1} + \cdots + \frac{1}{b_k}$ with distinct $a, b_1, \ldots, b_k \in A$.
-/
def IsMaxNoUnitFractionSumCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionSum A ∧ A.card = k} m

def erdos_301.parts.i.answer : ℝ := sorry

/--
Let $f(N)$ be the size of the largest $A \subseteq \{1, \ldots, N\}$ such that there are no
solutions to
$$\frac{1}{a} = \frac{1}{b_1} + \cdots + \frac{1}{b_k}$$
with distinct $a, b_1, \ldots, b_k \in A$. Estimate $f(N)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_301.parts.i (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoUnitFractionSumCard N (f N)) :
    Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 erdos_301.parts.i.answer) := by
  sorry

/--
In particular, is $f(N) = (\tfrac{1}{2} + o(1))N$?
-/
@[category research open, question, AMS 11]
theorem erdos_301.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoUnitFractionSumCard N (f N)) :
    Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  sorry

/--
Taking $A = \{1, \ldots, N\} \cap (N/2, N]$ gives the lower bound
$$f(N) \geq (1/2 + o(1))N.$$
-/
@[category research solved, AMS 11]
theorem erdos_301.variants.lower_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoUnitFractionSumCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := by
  sorry

/--
Wouter van Doorn proved the upper bound
$$f(N) \leq (25/28 + o(1))N.$$
-/
@[category research solved, AMS 11]
theorem erdos_301.variants.upper_twenty_five_twenty_eighths (f : ℕ → ℕ)
    (hf : ∀ N, IsMaxNoUnitFractionSumCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ ((25 : ℝ) / 28 + ε) * N := by
  sorry

/-- The empty set trivially satisfies `NoUnitFractionSum`. -/
@[category test, AMS 11]
theorem noUnitFractionSum_empty : NoUnitFractionSum ∅ := by
  intro a ha
  exact False.elim (Finset.notMem_empty a ha)

end Erdos301

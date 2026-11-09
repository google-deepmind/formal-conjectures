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
# Erdős Problem 791

Let $g(n)$ be the least size of a set $A \subseteq \{0,\ldots,n\}$ such that every
integer in $\{0,\ldots,n\}$ is a sum of two (not necessarily distinct) elements of $A$.
Erdős asked for an estimate of $g(n)$ and, in particular, whether
$g(n) \sim 2\sqrt{n}$. Mrose disproved this asymptotic, while the best known bounds
on the growth of $g(n)$ are due to Yu and Kohonen.

*References:*
- [Erdős Problems](https://www.erdosproblems.com/791), Problem 791.
- [Er73] P. Erdős, *Problems and results on combinatorial number theory*, A Survey of
  Combinatorial Theory (1973), 117–138.
- [Mr79] A. Mrose, *Untere Schranken für die Reichweiten von Extremalbasen fester Ordnung*
  (German), Abh. Math. Sem. Univ. Hamburg **48** (1979), 118–124.
- [Yu15] Gang Yu, *A new upper bound for finite additive $h$-bases*, J. Number Theory
  **156** (2015), 95–104. <https://doi.org/10.1016/j.jnt.2015.04.007>
- [Ko17] Jukka Kohonen, *An improved lower bound for finite additive 2-bases*, J. Number
  Theory **174** (2017), 518–524. <https://doi.org/10.1016/j.jnt.2016.11.011>
- [OEIS] [A066063](https://oeis.org/A066063), the sequence of values of $g(n)$.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos791

/-- `A` is a basis for `n` if $A \subseteq \{0, \ldots, n\}$ and every $m \in \{0, \ldots, n\}$
is a sum $a + b$ with $a, b \in A$. The two summands may be equal. -/
def IsBasis (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range (n + 1) ∧ ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m

/-- $g(n)$ is the smallest size of a basis for $n$. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset ℕ, IsBasis n A ∧ A.card = k}

/-- The unknown asymptotic formula for $g(n)$. -/
def erdos_791.parts.i.answer : ℕ → ℝ := sorry

/--
Let $g(n)$ be minimal such that there exists $A \subseteq \{0, \ldots, n\}$ of size $g(n)$
with $\{0, \ldots, n\} \subseteq A + A$. Estimate $g(n)$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_791.parts.i : (fun n ↦ (g n : ℝ)) ~[atTop] erdos_791.parts.i.answer := by
  sorry

/--
Let $g(n)$ be minimal such that there exists $A \subseteq \{0, \ldots, n\}$ of size $g(n)$
with $\{0, \ldots, n\} \subseteq A + A$. Is it true that $g(n) \sim 2n^{1/2}$?

Mrose [Mr79] proved that it is not.
-/
@[category research solved, question, AMS 5 11]
theorem erdos_791.parts.ii : ¬ (fun n ↦ (g n : ℝ)) ~[atTop] (fun n ↦ 2 * Real.sqrt n) := by
  sorry

/-- $\{0, 1\}$ is a basis for $2$, since $0 + 0 = 0$, $0 + 1 = 1$ and $1 + 1 = 2$. -/
@[category test, AMS 5 11]
theorem basis_two : IsBasis 2 {0, 1} := by
  unfold IsBasis
  decide

/-- $\{0, 1\}$ is not a basis for $3$, since its largest sum is $2$. -/
@[category test, AMS 5 11]
theorem not_basis_three : ¬ IsBasis 3 {0, 1} := by
  unfold IsBasis
  decide

/-- $\{0, 1, 2\}$ is a basis for $3$, so $g(3) \leq 3$. -/
@[category test, AMS 5 11]
theorem g_three_le : g 3 ≤ 3 :=
  Nat.sInf_le ⟨{0, 1, 2}, by unfold IsBasis; decide, rfl⟩

end Erdos791

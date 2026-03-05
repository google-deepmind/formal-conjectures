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
# Erdős Problem 475

Let $p$ be a prime. Is it true that every subset $A \subseteq \mathbb{F}_p \setminus \{0\}$ admits
a sequencing $a_1, \ldots, a_t$ such that all partial sums $\sum_{k=1}^{m} a_k$ are distinct?

*Reference:* [erdosproblems.com/475](https://www.erdosproblems.com/475)
-/

open Finset BigOperators

namespace Erdos475

/--
The partial sum of a sequence $f$ at index $m$: the sum $f(0) + f(1) + \cdots + f(m)$.
-/
noncomputable def partialSum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin n → α) (m : Fin n) : α :=
  (univ.filter (fun i : Fin n => i ≤ m)).sum f

/--
Erdős-Graham Conjecture on sequenceable sets in $\mathbb{F}_p$ (Problem 475):
Let $p$ be a prime. Given any finite set $A \subseteq \mathbb{F}_p \setminus \{0\}$, there always
exists a rearrangement $A = \{a_1, \ldots, a_t\}$ such that all partial sums
$\sum_{1 \le k \le m} a_k$ are distinct, for all $1 \le m \le t$.

Such an ordering is called a "valid ordering" or "sequencing" of $A$.
Graham proved the case $t = p - 1$.
-/
@[category research open, AMS 5 11]
theorem erdos_475 (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p))
    (hA : ∀ a ∈ A, a ≠ 0) :
    ∃ f : Fin A.card → ZMod p,
      (∀ i, f i ∈ A) ∧
      Function.Injective f ∧
      Function.Injective (partialSum f) := by
  sorry

end Erdos475

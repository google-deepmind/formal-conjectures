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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Analysis.Asymptotics.Asymptotics

/-!
# Erdős Problem 425

*Reference:* [erdosproblems.com/425](https://www.erdosproblems.com/425)

Let $F(n)$ be the maximum possible size of a subset $A\subseteq\{1,\ldots,n\}$
such that the products $ab$ are distinct for all $a<b$.
Is there a constant $c$ such that
\[
F(n)=\pi(n)+(c+o(1))n^{3/4}(\log n)^{-3/2}?
\]
If $A\subseteq \{1,\ldots,n\}$ is such that all products $a_1\cdots a_r$ are distinct
for $a_1<\cdots <a_r$ then is it true that
\[
\lvert A\rvert \leq \pi(n)+O(n^{(r+1)/(2r)})?
\]
-/

namespace Erdos425

open Finset Real Asymptotics

/--
A subset `A` of `{1,…,n}` has distinct pair products if for all `a,b,c,d ∈ A`
with `a < b` and `c < d`, we have `(a,b) ≠ (c,d) → a*b ≠ c*d`.
-/
def hasDistinctPairProducts (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
  a < b → c < d → (a ≠ c ∨ b ≠ d) → a * b ≠ c * d

/--
The maximum size of a subset `A ⊆ {1,…,n}` with distinct pair products.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup { A.card | A : Finset ℕ, ∀ x ∈ A, x ≤ n ∧ hasDistinctPairProducts A }

/--
A subset `A` has distinct `r`-fold products (for all `r`-tuples of distinct elements)
if every product of `r` distinct elements is unique.
-/
def hasDistinctRProducts (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ (s t : Finset ℕ) (hs : s ⊆ A) (ht : t ⊆ A) (hs' : s.card = r) (ht' : t.card = r)
    (h : s ≠ t),
    ∏ i in s, i ≠ ∏ i in t, i

/--
Conjecture: There exists a constant `c` such that
\[
F(n) = \pi(n) + (c+o(1)) n^{3/4} (\log n)^{-3/2}.
\]
We state this as an asymptotic equivalence with an unspecified constant `c`.
-/
@[category research open, AMS 52]
theorem erdos_425_main (c : ℝ) :
    (fun n => (F n : ℝ) - (π n : ℝ)) = (fun n => c * (n : ℝ)^(3/4) / (Real.log n)^(3/2)) +
      o(fun n => (n : ℝ)^(3/4) / (Real.log n)^(3/2)) := by
  sorry

/--
Conjecture: For any fixed `r ≥ 2`, if `A ⊆ {1,…,n}` has all `r`-fold products of
distinct elements distinct, then `|A| ≤ π(n) + O(n^{(r+1)/(2r)})`.
-/
@[category research open, AMS 52]
theorem erdos_425_r (r : ℕ) (hr : r ≥ 2) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
    (∀ x ∈ A, x ≤ n) → hasDistinctRProducts r A →
    (A.card : ℝ) ≤ (π n : ℝ) + C * (n : ℝ)^((r + 1 : ℝ) / (2 * r : ℝ)) := by
  sorry

end Erdos425

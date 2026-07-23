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
# Erdős Problem 788

*Reference:* [erdosproblems.com/788](https://www.erdosproblems.com/788)
-/

namespace Erdos788

/-- The integer interval `I_n = (n, 2n) ∩ ℕ`. -/
def I (n : ℕ) : Finset ℕ := Finset.Ioo n (2 * n)

/-- The integer interval `J_n = (2n, 4n) ∩ ℕ`. -/
def J (n : ℕ) : Finset ℕ := Finset.Ioo (2 * n) (4 * n)

/-- `C` is `B`-admissible: it lies in `I n`, and no sum of two distinct members
of `C` belongs to `B`. -/
def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧ ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

/-- The universal guarantee at threshold `t`: every `B ⊆ J n` admits an
admissible `C` with `t ≤ |B| + |C|`. -/
def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n → ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

/-- A uniform finite upper bound for every score `|B| + |C|`. -/
def scoreBound (n : ℕ) : ℕ := (J n).card + (I n).card

/-- The largest natural-number threshold with the universal property. -/
noncomputable def fNat (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

/-- `f(n)`: the largest integer `t` such that for every `B ⊆ (2n, 4n)` there is
a `C ⊆ (n, 2n)` with `c₁ + c₂ ∉ B` for all distinct `c₁, c₂ ∈ C` and
`|C| + |B| ≥ t`. -/
noncomputable def f (n : ℕ) : ℤ := (fNat n : ℤ)

/-- The exponent `1/2` conclusion `f(n) = n^{1/2 + o(1)}`, with full `ε`
quantifiers. -/
def HasExponentOneHalf : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε)

/--
Let $f(n)$ be maximal such that: if $B\subseteq (2n,4n)\cap \mathbb{N}$ then there
exists some $C\subseteq (n,2n)\cap \mathbb{N}$ such that $c_1+c_2\not\in B$ for all
$c_1\neq c_2\in C$ and $\lvert C\rvert+\lvert B\rvert \geq f(n)$. Estimate $f(n)$.

The answer is $f(n) = n^{1/2+o(1)}$. The linked proof establishes the sharper
two-sided bound `(1/2000)·√(n log n) ≤ f(n) ≤ n^{1/2 + O((loglog n / log n)^{1/3})}`,
of which `HasExponentOneHalf` is the exponent consequence.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/ShouqiaoW/erdos/blob/f2ae0edb45cbdb257e135d51ef855f64caeb348b/788/lean/Erdos788/FinalTheorem.lean"]
theorem erdos_788 : HasExponentOneHalf := by
  sorry

end Erdos788

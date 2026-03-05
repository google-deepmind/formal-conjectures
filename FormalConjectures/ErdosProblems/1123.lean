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
# Erdős Problem 1123

*Reference:* [erdosproblems.com/1123](https://www.erdosproblems.com/1123)

Let $B_1$ be the Boolean algebra of sets of integers modulo sets of density $0$
and let $B_2$ be the Boolean algebra of sets modulo sets of logarithmic density $0$.
Are $B_1$ and $B_2$ isomorphic?

[JuKr84] Just, W. and Krawczyk, A., *On certain Boolean algebras $\mathcal{P}(\omega)/I$*,
Trans. Amer. Math. Soc. 285 (1984), 411-429.
-/

open Filter Finset Classical

open scoped BigOperators

namespace Erdos1123

/-- The natural (asymptotic) density of a set $A \subseteq \mathbb{N}$ is zero if
$|A \cap \{0, \ldots, n\}| / (n+1) \to 0$ as $n \to \infty$. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    ((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ) / ((n : ℝ) + 1))
    atTop (nhds 0)

/-- The logarithmic density of a set $A \subseteq \mathbb{N}$ is zero if
$(1/\log n) \cdot \sum_{\substack{k \in A \\ 1 \leq k \leq n}} 1/k \to 0$
as $n \to \infty$. -/
def HasLogDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    (∑ k ∈ Finset.filter (· ∈ A) (Finset.Icc 1 n), (1 : ℝ) / (k : ℝ)) /
    Real.log (n : ℝ))
    atTop (nhds 0)

/-- Two sets of naturals are equivalent mod natural-density-$0$ sets
iff their symmetric difference has natural density zero. -/
def NatDensityEquiv (A B : Set ℕ) : Prop :=
  HasNaturalDensityZero (symmDiff A B)

/-- Two sets of naturals are equivalent mod log-density-$0$ sets
iff their symmetric difference has logarithmic density zero. -/
def LogDensityEquiv (A B : Set ℕ) : Prop :=
  HasLogDensityZero (symmDiff A B)

/-- Natural density equivalence is an equivalence relation. -/
axiom natDensityEquiv_equivalence : Equivalence NatDensityEquiv

/-- Logarithmic density equivalence is an equivalence relation. -/
axiom logDensityEquiv_equivalence : Equivalence LogDensityEquiv

/-- The equivalence relation on $\operatorname{Set} \mathbb{N}$ given by natural density zero. -/
def natDensitySetoid : Setoid (Set ℕ) where
  r := NatDensityEquiv
  iseqv := natDensityEquiv_equivalence

/-- The equivalence relation on $\operatorname{Set} \mathbb{N}$ given by logarithmic density zero. -/
def logDensitySetoid : Setoid (Set ℕ) where
  r := LogDensityEquiv
  iseqv := logDensityEquiv_equivalence

/-- $B_1$: the Boolean algebra of sets of integers modulo sets of natural density $0$. -/
def BoolAlgModNatDensity : Type := Quotient natDensitySetoid

/-- $B_2$: the Boolean algebra of sets of integers modulo sets of logarithmic density $0$. -/
def BoolAlgModLogDensity : Type := Quotient logDensitySetoid

/-- The quotient of sets of integers by natural density zero sets forms a Boolean algebra. -/
axiom instBooleanAlgebraBoolAlgModNatDensity : BooleanAlgebra BoolAlgModNatDensity

/-- The quotient of sets of integers by logarithmic density zero sets forms a Boolean algebra. -/
axiom instBooleanAlgebraBoolAlgModLogDensity : BooleanAlgebra BoolAlgModLogDensity

noncomputable instance : BooleanAlgebra BoolAlgModNatDensity :=
  instBooleanAlgebraBoolAlgModNatDensity
noncomputable instance : BooleanAlgebra BoolAlgModLogDensity :=
  instBooleanAlgebraBoolAlgModLogDensity

/--
Let $B_1$ be the Boolean algebra of sets of integers modulo sets of density $0$
and let $B_2$ be the Boolean algebra of sets modulo sets of logarithmic density $0$.
Is $B_1$ isomorphic to $B_2$?

Note: This is independent of ZFC. Just and Krawczyk [JuKr84] proved under the
continuum hypothesis that these two algebras ARE isomorphic.
-/
@[category research open, AMS 06 11]
theorem erdos_1123 :
    answer(sorry) ↔ Nonempty (BoolAlgModNatDensity ≃o BoolAlgModLogDensity) := by
  sorry

end Erdos1123

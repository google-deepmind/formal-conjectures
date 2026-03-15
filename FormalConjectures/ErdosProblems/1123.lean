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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 1123

*Reference:* [erdosproblems.com/1123](https://www.erdosproblems.com/1123)

A problem of Erdős and Ulam. Let $B_1$ be the Boolean algebra of sets of integers modulo sets
of density $0$ and let $B_2$ be the Boolean algebra of sets modulo sets of logarithmic
density $0$. Are $B_1$ and $B_2$ isomorphic? Erdős offered $100 for a proof or disproof.

This is independent of ZFC: Just and Krawczyk [JuKr84] proved under the continuum hypothesis
that $B_1 \cong B_2$, while Farah [Fa00] proved under OCA + MA that $B_1 \not\cong B_2$.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981), 27-35.

[VMR80] van Douwen, E., Monk, J. and Rubin, M., _Some questions about Boolean algebras_.
Algebra Universalis **10** (1980), 220-243.

[JuKr84] Just, W. and Krawczyk, A., _On certain Boolean algebras $\mathcal{P}(\omega)/I$_.
Trans. Amer. Math. Soc. **285** (1984), 411-429.

[ARS85] Abraham, U., Rubin, M. and Shelah, S., _On the consistency of some partition theorems
for continuous colorings, and the structure of $\aleph_1$-dense real order types_.
Ann. Pure Appl. Logic (1985), 123-206.

[Fa00] Farah, I., _Analytic quotients: theory of liftings for quotients over analytic ideals
on the integers_. Mem. Amer. Math. Soc. (2000), xvi+177.
-/

open Filter Classical

namespace Erdos1123

/-- Two sets of naturals are equivalent mod natural-density-$0$ sets
iff their symmetric difference has natural density zero. -/
def NatDensityEquiv (A B : Set ℕ) : Prop :=
  Set.HasDensity (symmDiff A B) 0

/-- Two sets of naturals are equivalent mod log-density-$0$ sets
iff their symmetric difference has logarithmic density zero. -/
def LogDensityEquiv (A B : Set ℕ) : Prop :=
  Set.HasLogDensity (symmDiff A B) 0

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
A problem of Erdős and Ulam. Let $B_1$ be the Boolean algebra of sets of integers modulo sets
of density $0$ and let $B_2$ be the Boolean algebra of sets modulo sets of logarithmic
density $0$. Is $B_1$ isomorphic to $B_2$?

This is independent of ZFC. Just and Krawczyk [JuKr84] proved under the continuum hypothesis
that $B_1 \cong B_2$. Farah [Fa00] proved under OCA + MA that $B_1 \not\cong B_2$.
-/
@[category research open, AMS 06 11]
theorem erdos_1123 :
    answer(sorry) ↔ Nonempty (BoolAlgModNatDensity ≃o BoolAlgModLogDensity) := by
  sorry

end Erdos1123

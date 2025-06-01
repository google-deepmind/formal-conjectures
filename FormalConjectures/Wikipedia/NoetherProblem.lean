/-
Copyright 2025 The Formal Conjectures Authors.

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
# Rational_variety

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Rational_variety)
-/
/--
A rational field extension is a field extension `L/K` isomorphic
to a field of rational functions (in some arbitrary number of indeterminates.)
-/
class IsRationalExtension (K L ι : Type*)
    [Field K] [Field L] [Algebra K L] where
  pure_transcendental :
    Nonempty (L ≃ₐ[K] ((FractionRing (MvPolynomial ι K))))

/-- If the index set `ι` is empty, then `IsRationalExtension K L ι` means that
`K, L` are isomorphic as `K` algebras. -/
@[category test, AMS 12]
example (K L ι : Type*) [Field K] [Field L] [Algebra K L] [IsEmpty ι]
    [IsRationalExtension K L ι] :
    Nonempty (L ≃ₐ[K] K) := by
  set a : L ≃ₐ[K] (FractionRing (MvPolynomial ι K)) :=
    Classical.choice IsRationalExtension.pure_transcendental
  set b : (MvPolynomial ι K) ≃ₐ[K] K := MvPolynomial.isEmptyAlgEquiv K ι
  set c : FractionRing (MvPolynomial ι K) ≃ₐ[K] K :=
    IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial ι K)) K b
  apply Nonempty.intro (a.trans c)


/--
We say that a rational extension `L` of `K` has the _Noether Property_
if for any finite subgroup `H` of the Galois group of `L`, the fixed field
`L^H` is also a rational extension.
-/
def HasNoetherProperty (K L ι : Type) [Field K] [Field L] [Fintype ι]
    [Algebra K L] [IsRationalExtension K L ι] : Prop :=
  ∀ H : Subgroup (L ≃ₐ[K] L), Finite H → ∃ ι' : Type,
    IsRationalExtension K (IntermediateField.fixedField H) ι'

/--
The **Noether Problem**: let `L` be the field of rational functions in `n`
indeterminates over `K`. Is it true that `L/K` has the Noether property?

Solution: False.
-/
@[category research solved, AMS 12, AMS 14]
theorem noether_problem : ∃ (K L ι G : Type)
    (_ : Field K) (_ : Field L) (_ : Fintype ι) (_ : Algebra K L) (_ : IsRationalExtension K L ι),
    ¬ HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution in the two indeterminate case.
-/
@[category research solved, AMS 12, AMS 14]
theorem noether_problem.variants.two {K L ι G : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 2) :
    HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution in the three indeterminate case.
-/
@[category research solved, AMS 12, AMS 14]
theorem noether_problem.variants.three {K L ι G : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 3) :
    HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution in the four indeterminate case.
-/
@[category research solved, AMS 12, AMS 14]
theorem noether_problem.variants.four {K L ι G : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 4) :
    HasNoetherProperty K L ι := by
  sorry

/--
One can find a counterexample to the Noether Problem's claim by considering a
rational function field in 47 indeterminates.
-/
@[category research solved, AMS 12, AMS 14]
theorem noether_problem.variants.forty_seven :
    ∃ (K L ι G : Type)
    (_ :  Field K) (_ : Field L) (_ : Fintype ι) (_ : Algebra K L)
    (_ : IsRationalExtension K L ι),
    Fintype.card ι = 47 ∧ ¬ HasNoetherProperty K L ι := by
  sorry

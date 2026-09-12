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

import FormalConjecturesUtil

/-!
# Rational_variety

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Rational_variety)
-/

namespace NoetherProblem

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
theorem rationalExtension_empty_index (K L ι : Type*) [Field K] [Field L] [Algebra K L] [IsEmpty ι]
    [IsRationalExtension K L ι] :
    Nonempty (L ≃ₐ[K] K) := by
  set a : L ≃ₐ[K] (FractionRing (MvPolynomial ι K)) :=
    Classical.choice IsRationalExtension.pure_transcendental
  set b : (MvPolynomial ι K) ≃ₐ[K] K := MvPolynomial.isEmptyAlgEquiv K ι
  set c : FractionRing (MvPolynomial ι K) ≃ₐ[K] K :=
    IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial ι K)) K b
  apply Nonempty.intro (a.trans c)

/--
We say that a rational extension `L` of `K` in the indeterminates `ι` has the _Noether Property_
if, for every identification of `L` with the rational function field `K(X_i : i ∈ ι)`, the fixed
field `L^H` of every group `H` of `K`-automorphisms of `L` permuting the indeterminates `X_i` is
again a rational extension of `K`. Such a group `H` is necessarily finite.
-/
def HasNoetherProperty (K L ι : Type) [Field K] [Field L] [Fintype ι]
    [Algebra K L] [IsRationalExtension K L ι] : Prop :=
  ∀ (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K)) (H : Subgroup (L ≃ₐ[K] L)),
    (∀ h ∈ H, ∃ σ : Equiv.Perm ι, h = (AlgEquiv.autCongr e).symm
      (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ))) →
    ∃ ι' : Type, IsRationalExtension K (IntermediateField.fixedField H) ι'

/--
The **Noether Problem**: let `L` be the field of rational functions in `n`
indeterminates over `K`, and let `G` be a finite group permuting these indeterminates.
Is the fixed field `L^G` a rational extension of `K`, i.e. does `L/K` have the Noether property?

Solution: False.
-/
@[category research solved, AMS 12 14]
theorem noether_problem : answer(False) ↔ ∀ (K L ι : Type)
    [Field K] [Field L] [Fintype ι] [Algebra K L] [IsRationalExtension K L ι],
    HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution for groups permuting two indeterminates.
-/
@[category research solved, AMS 12 14]
theorem noether_problem.variants.two {K L ι : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 2) :
    HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution for groups permuting three indeterminates.
-/
@[category research solved, AMS 12 14]
theorem noether_problem.variants.three {K L ι : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 3) :
    HasNoetherProperty K L ι := by
  sorry

/--
The Noether problem has a positive solution for groups permuting four indeterminates.
-/
@[category research solved, AMS 12 14]
theorem noether_problem.variants.four {K L ι : Type}
    [Field K] [Field L] [Fintype ι] [Algebra K L]
    [IsRationalExtension K L ι] (hι : Fintype.card ι = 4) :
    HasNoetherProperty K L ι := by
  sorry

/--
One can find a counterexample to the Noether Problem's claim by considering a
group permuting the 47 indeterminates of a rational function field.
-/
@[category research solved, AMS 12 14]
theorem noether_problem.variants.forty_seven :
    ∃ (K L ι : Type)
    (_ :  Field K) (_ : Field L) (_ : Fintype ι) (_ : Algebra K L)
    (_ : IsRationalExtension K L ι),
    Fintype.card ι = 47 ∧ ¬ HasNoetherProperty K L ι := by
  sorry

end NoetherProblem

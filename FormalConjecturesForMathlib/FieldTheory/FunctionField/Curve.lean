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

public import FormalConjecturesForMathlib.FieldTheory.FunctionField.Genus

import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Curves presented by their function fields

Mathlib has no general theory of algebraic curves, so this file describes a curve over a field `K`
by its function field. The finitely generated field extensions $F / K$ of transcendence degree
$1$ correspond to the regular projective curves over $K$ ([Stacks], Theorem 53.2.6). If $K$ is
perfect, for example of characteristic zero, then such a curve is smooth, and it is geometrically
integral exactly when $K$ is algebraically closed in $F$. Under this dictionary the
closed points of the curve are the places of $F / K$, the degree of a closed point is the degree
of the place, and the set $X(K)$ of rational points is the set of places of degree $1$.

`FunctionField.CurveFunctionField K` bundles a function field with these conditions. Its genus
and its rational points are `FunctionField.CurveFunctionField.genus` and
`FunctionField.CurveFunctionField.rationalPlaces`. The projective line
`FunctionField.CurveFunctionField.projectiveLine` has a rational point, the place at infinity.

## References

- Henning Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer GTM 254,
  Chapter 1, https://doi.org/10.1007/978-3-540-76878-4
- [Stacks] The Stacks Project, Theorem 53.2.6, https://stacks.math.columbia.edu/tag/0BY1
-/

@[expose] public section

namespace FunctionField

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- `F` is the function field of a regular projective curve over `K`: `F / K` is a finitely
generated field extension of transcendence degree `1` in which `K` is algebraically closed. The
curve is smooth and geometrically integral when `K` is perfect, in particular whenever `K` is a
number field. -/
structure IsCurveFunctionField : Prop where
  /-- `F / K` is a finitely generated field extension. -/
  essFiniteType : Algebra.EssFiniteType K F
  /-- `F / K` has transcendence degree one. -/
  trdeg : Algebra.trdeg K F = 1
  /-- `K` is algebraically closed in `F`, that is, `K` is the full constant field of `F / K`. -/
  algebraicClosure_eq_bot : algebraicClosure K F = ⊥

/-- The rational function field `K(t)` is the function field of a curve, namely of the projective
line. -/
theorem isCurveFunctionField_ratFunc : IsCurveFunctionField K (RatFunc K) where
  essFiniteType :=
    have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
      Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  trdeg := by
    have : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (Polynomial K))
    have h := trdeg_add_eq (A := RatFunc K) K (Polynomial K)
    rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
    exact h.symm
  algebraicClosure_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ : ∃ c, x = RatFunc.C c := by
      by_contra h
      exact RatFunc.transcendental_of_ne_C x h (mem_algebraicClosure_iff.1 hx)
    exact ⟨c, rfl⟩

/-- A curve over `K`, presented by its function field. Bundling `IsCurveFunctionField` with the
field keeps `genus` and `rationalPlaces` away from extensions on which they would return junk
values, and lets statements quantify over curves rather than over carrier types. -/
structure CurveFunctionField.{u} (K : Type u) [Field K] where
  -- A function field of one variable over `K : Type u` is finitely generated over `K`, so it has
  -- a presentation as a localisation of a quotient of `MvPolynomial (Fin n) K`. We therefore lose
  -- no generality by taking `carrier : Type u`, and this keeps a bound that is quantified over all
  -- curves from depending on a universe parameter.
  /-- The function field of the curve. -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  /-- The carrier really is the function field of a curve. -/
  isCurveFunctionField : IsCurveFunctionField K carrier

attribute [instance] CurveFunctionField.field CurveFunctionField.algebra

namespace CurveFunctionField

/-- The projective line over `K`, presented by its function field `K(t)`. -/
noncomputable def projectiveLine : CurveFunctionField K where
  carrier := RatFunc K
  isCurveFunctionField := isCurveFunctionField_ratFunc K

/-- Curves exist: the projective line is one. -/
example : Nonempty (CurveFunctionField K) :=
  ⟨projectiveLine K⟩

variable {K}

/-- The genus of a curve. -/
noncomputable def genus (C : CurveFunctionField K) : ℕ :=
  FunctionField.genus K C.carrier

/-- The rational points of a curve: the places of its function field of degree `1`. -/
def rationalPlaces (C : CurveFunctionField K) : Set (Place K C.carrier) :=
  {P | P.degree = 1}

/-- The rational points of a curve are its places of degree one. -/
theorem mem_rationalPlaces {C : CurveFunctionField K} {P : Place K C.carrier} :
    P ∈ C.rationalPlaces ↔ P.degree = 1 := Iff.rfl

variable (K)

/-- The place at infinity is a rational point of the projective line. -/
theorem atInfty_mem_rationalPlaces_projectiveLine [DecidableEq (RatFunc K)] :
    Place.atInfty K ∈ (projectiveLine K).rationalPlaces :=
  Place.degree_atInfty K

/-- The projective line has a rational point. This checks `Place.degree` on an example. -/
example : (projectiveLine K).rationalPlaces.Nonempty := by
  classical exact ⟨_, atInfty_mem_rationalPlaces_projectiveLine K⟩

end CurveFunctionField

end FunctionField

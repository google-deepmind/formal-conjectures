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
# Gottschalk's surjunctivity conjecture

A group $G$ is *surjunctive* if every injective, continuous, $G$-equivariant map
$A^G \to A^G$ (for any finite alphabet $A$) is surjective.

Here equivariance is with respect to the left shift action of $G$ on $A^G$,
defined by $(g \cdot x)(h) = x(g^{-1} h)$, and continuity is with respect to
the product topology on $A^G$ (where $A$ carries the discrete topology).

Gottschalk's conjecture (1973) states that every group is surjunctive.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Surjunctive_group)
- Gottschalk, W. H. (1973), "Some general dynamical notions"
-/

namespace GottschalkSurjunctivity

variable (G : Type*) [Group G]

/-- The left shift of `x : G → A` by `g : G`, defined by `(shift g x)(h) = x(g⁻¹ * h)`.
This is the standard left shift action of `G` on `A^G`. We define it as a plain function
rather than a `MulAction` instance to avoid conflict with the pointwise `Pi.instMulAction`. -/
def shift {A : Type*} (g : G) (x : G → A) : G → A :=
  fun h => x (g⁻¹ * h)

@[simp]
theorem shift_apply {A : Type*} (g : G) (x : G → A) (h : G) :
    shift G g x h = x (g⁻¹ * h) := rfl

@[simp]
theorem shift_one {A : Type*} (x : G → A) :
    shift G 1 x = x := by
  ext h; simp [shift]

theorem shift_mul {A : Type*} (g₁ g₂ : G) (x : G → A) :
    shift G (g₁ * g₂) x = shift G g₁ (shift G g₂ x) := by
  ext h; simp [shift, mul_assoc]

/-- A map `τ : (G → A) → (G → A)` is *equivariant* (with respect to the left shift action)
if `τ(shift g x) = shift g (τ x)` for all `g : G` and `x : G → A`. -/
def IsShiftEquivariant {A : Type*} (τ : (G → A) → (G → A)) : Prop :=
  ∀ (g : G) (x : G → A), τ (shift G g x) = shift G g (τ x)

/-- A group `G` is *surjunctive* if for every finite nonempty type `A`, every injective,
continuous, shift-equivariant map `(G → A) → (G → A)` is also surjective.

Continuity is with respect to the product topology on `G → A` where `A` carries the
discrete topology. -/
def IsSurjunctive : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A]
    (τ : (G → A) → (G → A)),
    @Continuous (G → A) (G → A) Pi.topologicalSpace Pi.topologicalSpace τ →
    IsShiftEquivariant G τ →
    Function.Injective τ →
    Function.Surjective τ

/-- **Gottschalk's surjunctivity conjecture** (1973): every group is surjunctive.
That is, for every group `G` and every finite alphabet `A`, every injective cellular
automaton on `A^G` is surjective. -/
@[category research open, AMS 20 37]
theorem gottschalk_surjunctivity_conjecture (G : Type) [Group G] :
    IsSurjunctive G := by
  sorry

/-- Every finite group is surjunctive. This is a classical result: an injective
endomorphism of a finite set is surjective. -/
@[category research solved, AMS 20 37]
theorem isSurjunctive_of_finite (G : Type) [Group G] [Finite G] :
    IsSurjunctive G := by
  sorry

end GottschalkSurjunctivity

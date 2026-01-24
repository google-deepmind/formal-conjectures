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

open Ring

/-!
# Jacobson Conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Jacobson's_conjecture)
* [He1965]: Herstein, I. N. (1965), "A counterexample in Noetherian rings",
  Proceedings of the National Academy of Sciences of the United States of America, 54 (4): 1036–1037
  https://pmc.ncbi.nlm.nih.gov/articles/PMC219788/
* [Ja1956]: Jacobson, Nathan. Structure of rings. Vol. 37. American Mathematical Soc., 1956.
* [Le1977]: Lenagan, T. H. (1977), "Noetherian rings with Krull dimension one",
  J. London Math. Soc. Series 2, 15 (1): 41–47
  https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/s2-15.1.41
-/

universe u

namespace Jacobson

/-- A right ideal in a semiring $R$ is an additive submonoid $s$ such that
$a * b \in s$ whenever $a \in s$. If $R$ is a ring, then $s$ is an additive subgroup. -/
structure RightIdeal (R : Type u) [Semiring R] : Type u extends AddSubmonoid R where
  mem_mul : ∀ {a : R} (b : R), a ∈ carrier → a * b ∈ carrier

namespace RightIdeal

/-- In a commutative (semi-)ring, every right ideal is a left ideal -/
@[category test, AMS 16]
abbrev toIdeal {R : Type u} [CommSemiring R] (I : RightIdeal R) : Ideal R where
  carrier := I.carrier
  add_mem' := I.add_mem'
  zero_mem' := I.zero_mem'
  smul_mem' := by
    intro x y yh
    rw [smul_eq_mul, mul_comm]
    exact I.mem_mul x yh

/-- In a commutative (semi-)ring, every left ideal is a right ideal -/
@[category test, AMS 16]
abbrev toRightIdeal {R : Type u} [CommSemiring R] (I : Ideal R) : RightIdeal R where
  carrier := I.carrier
  add_mem' := I.add_mem'
  zero_mem' := I.zero_mem'
  mem_mul := by
    intro x y xh
    rw [mul_comm, ← smul_eq_mul]
    exact I.smul_mem' y xh

variable (R : Type u) [Semiring R]

@[category test, AMS 16]
instance setLike : SetLike (RightIdeal R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

variable {R}

@[category test, AMS 16, ext]
theorem ext {I J : RightIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

variable (R)

/-- The intersection of right ideals is a right ideal-/
@[category test, AMS 16]
abbrev OfInter {R : Type u} [Semiring R] (s : Set (RightIdeal R)) : RightIdeal R where
  carrier := ⋂ I ∈ s, I.carrier
  add_mem' := by
    intro a b ha hb t ⟨I, hI⟩
    simp only at hI
    rw [← hI]
    simp at *
    intro h'
    exact AddSubmonoid.add_mem I.toAddSubmonoid (ha I h') (hb I h')
  zero_mem' := by simp
  mem_mul := by
    intro a b ah
    simp only [Set.mem_iInter, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup] at *
    intro I hI
    apply I.mem_mul
    exact ah I hI

/-- The right ideals are an InfSet -/
@[category test, AMS 16]
instance InfSet : InfSet (RightIdeal R) where
  sInf s := OfInter s

/-- The entire ring is a right ideal -/
@[category test, AMS 16]
abbrev ofRing : RightIdeal R where
  carrier := .univ
  add_mem' := fun a _ ↦ a
  zero_mem' := trivial
  mem_mul := by
    intros
    exact Set.mem_univ _

@[category test, AMS 16]
instance OrderTop : OrderTop (RightIdeal R) where
  top := .ofRing R
  le_top := by
    intros
    exact fun ⦃_⦄ _ ↦ trivial

variable {R}

/-- A right ideal is maximal if it is maximal in the collection of proper ideals. -/
@[category test, AMS 16]
class IsMaximal (I : RightIdeal R) : Prop where
  /-- The maximal right ideal is a coatom in the ordering on right ideals; that is, it is not the entire ring,
  and there are no other proper ideals strictly containing it. -/
  out : IsCoatom I

end RightIdeal

/-- A right Noetherian ring -/
@[inline]
abbrev IsRightNoetherianRing (R : Type u) [Semiring R] : Prop :=
  WellFoundedGT (RightIdeal R)

/-- The Jacobson conjecture for a ring $R$: $\bigcap_{n \in \mathbb{N}} J^n = \{0\}$
where $J$ is the Jacobson radical of $R$. -/
def JacobsonConjectureFor (R : Type u) [Ring R] : Prop :=
  ⋂ n : ℕ, (↑((jacobson R) ^ n) : Set R) = {0}

/-- The Jacobson conjecture (in its modern form):
In a (noncommutative) ring which is left and right Noetherian,
the intersection of the powers of the Jacobson ideal is trivial -/
@[category research open, AMS 16]
theorem jacobson_conjecture :
    answer(sorry) ↔ ∀ (R : Type) [Ring R] [IsNoetherianRing R] [IsRightNoetherianRing R],
      JacobsonConjectureFor R := by
  sorry

/-- For commutative rings this is the case as a consequence of Krull's intersection theorem. -/
@[category graduate, AMS 13 16]
theorem jacobson_conjecture_of_comm_ring (R : Type u) [CommRing R] [IsNoetherianRing R] :
    JacobsonConjectureFor R := by
  sorry

/-- Originally, on page 200 of [Ja1956], Jacobson asked if the Jacobson conjecture holds for all left
Noetherian rings. However in [He1965] Herstein constructs a left Noetherian ring for which the
Jacobson conjecture does not hold. -/
@[category research open, AMS 16]
theorem jacobson_conjecture_of_left_noetherian :
    answer(False) ↔ ∀ (R : Type) [Ring R] [IsNoetherianRing R], JacobsonConjectureFor R := by
  sorry

/- In [Le1977] Lenagan shows the Jacobson conjecture holds for left and right Noetherian rings
with Krull dimension $1$. -/
-- TODO: Add this result. Note that we do not have Krull dimension for noncommutative rings yet.

end Jacobson

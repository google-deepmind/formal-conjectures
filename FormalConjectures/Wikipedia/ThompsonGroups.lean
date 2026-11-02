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

public import FormalConjecturesUtil

/-!
# Amenability of Thompson's group $F$

Thompson's group $F$ is the group, under composition, of the increasing homeomorphisms of
$[0, 1]$ that are piecewise linear with finitely many dyadic breakpoints and with slopes powers
of $2$. The conjecture that $F$ is not amenable goes back to Thompson and was popularized by
Geoghegan [CFP96]. Brin and Squier showed that $F$ has no non-abelian free subgroup [BS85], so
nonamenability cannot come from a free subgroup.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Thompson_groups)
- [BS85] M. G. Brin and C. C. Squier, *Groups of piecewise linear homeomorphisms of the real
  line*, Invent. Math. 79 (1985), 485–498.
- [CFP96] J. W. Cannon, W. J. Floyd and W. R. Parry, *Introductory notes on Richard Thompson's
  groups*, Enseign. Math. (2) 42 (1996), 215–256.
- [OAI26] OpenAI, *Thompson's group F is nonamenable*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thompsons-group-F-is-nonamenable-September-23-2026/paper.pdf
-/

@[expose] public section

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonGroups

/-- The unit interval `[0, 1]`. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- `0 ∈ [0, 1]`. -/
def unitIntervalZero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩

/-- `1 ∈ [0, 1]`. -/
def unitIntervalOne : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

/-- A homeomorphism of `[0, 1]`. -/
structure IntervalHomeomorph where
  /-- The underlying homeomorphism. -/
  toHomeomorph : UnitInterval ≃ₜ UnitInterval

namespace IntervalHomeomorph

instance : CoeFun IntervalHomeomorph (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun f => f.toHomeomorph⟩

end IntervalHomeomorph

/-- `x` is a dyadic rational. -/
def IsDyadic (x : ℝ) : Prop :=
  ∃ (k : ℤ) (n : ℕ), x = (k : ℝ) / (2 : ℝ) ^ n

/-- A subdivision of `[0, 1]` at dyadic points on whose pieces `f` is affine with slope a power
of `2`. -/
structure DyadicPLWitness (f : IntervalHomeomorph) where
  /-- The number of pieces. -/
  pieceCount : ℕ
  positive : 0 < pieceCount
  /-- The breakpoints. -/
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  /-- The slope on the `i`-th piece is `2 ^ exponent i`. -/
  exponent : Fin pieceCount → ℤ
  affine : ∀ (i : Fin pieceCount) (x : UnitInterval),
    knots i.castSucc ≤ x → x ≤ knots i.succ →
    (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
      (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

/-- `f` is piecewise linear with dyadic breakpoints and slopes powers of `2`. -/
def HasDyadicPLPieces (f : IntervalHomeomorph) : Prop := Nonempty (DyadicPLWitness f)

/-- The underlying set of Thompson's group `F`. -/
def F := {f : IntervalHomeomorph // StrictMono f ∧ HasDyadicPLPieces f}

/-- Bounded real functions on `G`. -/
abbrev BoundedReal (G : Type uG) := lp (fun _ : G => ℝ) ∞

variable {G : Type uG} [Group G]

/-- `f ↦ (g ↦ f (h * g))`. -/
def leftPull (h : G) : BoundedReal G →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (h * g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (h * g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

/-- A left-invariant mean on `G`. A group is amenable if it has one. -/
structure InvariantMean (G : Type uG) [Group G] where
  /-- The mean as a linear functional on bounded functions. -/
  toLinearMap : BoundedReal G →ₗ[ℝ] ℝ
  positive : ∀ f : BoundedReal G, (∀ g, 0 ≤ f g) → 0 ≤ toLinearMap f
  normalized : toLinearMap 1 = 1
  left_invariant : ∀ (h : G) (f : BoundedReal G),
    toLinearMap (leftPull h f) = toLinearMap f

set_option linter.style.formal_proof_palomar false in
/--
**Thompson's group $F$ is not amenable.** There is a group structure on `F` whose
multiplication is composition, and the resulting group has no left-invariant mean.

The group structure is unique, since an element of `F` is determined by its underlying function.

Whether $F$ is amenable was a long-standing open question. An internal OpenAI model proved that
it is not in September 2026 [OAI26]; see the linked Lean proof.
-/
@[category research solved, AMS 20 43, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/Thompson/Main.lean#L69"]
theorem thompson_F_nonamenable :
    ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F) := by
  sorry

end ThompsonGroups

end

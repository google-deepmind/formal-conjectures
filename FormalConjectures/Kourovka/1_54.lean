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
# Kourovka Notebook Problem 1.54 — Bi-orderings of free metabelian groups

A. I. Kokorin asked for a description of all linear orderings of a finitely generated free
metabelian group. Issue #1925 asks for the homeomorphism type of the space of bi-orderings.
In the Sikora topology, a basic neighborhood specifies the signs of finitely many group elements.

Wang proved that this space is a Cantor set in every finite rank at least two (Theorem C).
In rank two he also proved that the derived subgroup is convex in every bi-order (Theorem A).

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300), Problem 1.54.
- [Formal Conjectures issue #1925](https://github.com/google-deepmind/formal-conjectures/issues/1925).
- A. S. Sikora, [Topology on the spaces of orderings of groups](https://arxiv.org/abs/math/0111002),
  Bull. London Math. Soc. 36 (2004), 519–526.
- W. Wang, [Orders on free metabelian groups](https://arxiv.org/abs/2210.14630),
  J. Group Theory 27 (2024), 485–517, [published online in 2023](https://doi.org/10.1515/jgth-2022-0203).
-/

@[expose] public section

namespace Kourovka.«1.54»

variable {G : Type*} [Group G]

/-- The characteristic function of a strict positive cone. Off the identity, exactly one
of an element and its inverse is positive. The cone is closed under products and conjugation. -/
@[mk_iff]
structure IsBiOrderCone (p : G → Bool) : Prop where
  one : p 1 = false
  inv : ∀ g ≠ 1, p g⁻¹ = !(p g)
  mul : ∀ a b, p a = true → p b = true → p (a * b) = true
  conj : ∀ g x, p x = true → p (g * x * g⁻¹) = true

/-- Bi-orderings of a group, with the subspace topology from the product of discrete
two-point spaces indexed by the group. -/
abbrev BiOrdering (G : Type*) [Group G] := {p : G → Bool // IsBiOrderCone p}

namespace BiOrdering

/-- The strict comparison determined by the positive cone. -/
def lt (P : BiOrdering G) (a b : G) : Prop := P.val (a⁻¹ * b) = true

instance (P : BiOrdering G) : IsStrictTotalOrder G P.lt where
  irrefl a := by simp [lt, P.property.one]
  trans a b c hab hbc := by
    simpa [lt, mul_assoc] using P.property.mul _ _ hab hbc
  trichotomous a b hab hba := by
    by_contra h
    have hi := P.property.inv (a⁻¹ * b) (fun e => h (eq_of_inv_mul_eq_one e))
    simp [lt] at hab hba
    simp [hab, hba] at hi

/-- The induced strict order is invariant under both left and right multiplication. -/
@[category API, AMS 6 20]
theorem mul_lt_mul (P : BiOrdering G) (g h : G) {a b : G} (hab : P.lt a b) :
    P.lt (g * a * h) (g * b * h) := by
  simpa [lt, mul_assoc] using P.property.conj h⁻¹ (a⁻¹ * b) hab

/-- Conversely, every bi-invariant strict total order has a unique positive cone. -/
@[category API, AMS 6 20]
theorem existsUnique_of_order (r : G → G → Prop) [IsStrictTotalOrder G r]
    (hinv : ∀ g h a b, r (g * a * h) (g * b * h) ↔ r a b) :
    ∃! P : BiOrdering G, ∀ a b, P.lt a b ↔ r a b := by
  classical
  have left (g a b : G) : r (g * a) (g * b) ↔ r a b := by simpa using hinv g 1 a b
  let p (x : G) := decide (r 1 x)
  have cone : IsBiOrderCone p := by
    constructor
    · simp [p, irrefl_of r]
    · intro x hx
      have h : r 1 x⁻¹ ↔ r x 1 := by simpa using (left x 1 x⁻¹).symm
      simp only [p, ← decide_not, decide_eq_decide, h]
      exact ⟨fun h' => asymm_of r h', fun h' =>
        ((trichotomous_of r x 1).resolve_right (not_or.mpr ⟨hx, h'⟩))⟩
    · simp only [p, decide_eq_true_eq]
      intro a b ha hb
      exact trans_of r ha (by simpa using (left a 1 b).mpr hb)
    · simp only [p, decide_eq_true_eq]
      intro g x hx
      simpa using (hinv g g⁻¹ 1 x).mpr hx
  refine ⟨⟨p, cone⟩, fun a b => ?_, fun Q hQ => ?_⟩
  · simpa [lt, p] using left a⁻¹ a b
  · apply Subtype.ext
    funext x
    change Q.val x = decide (r 1 x)
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    simpa [lt] using hQ 1 x

/-- The cone axioms cut out a closed subset of the product: each individual constraint
tests only finitely many signs. -/
@[category API, AMS 6 20 54]
theorem isClosed_isBiOrderCone : IsClosed {p : G → Bool | IsBiOrderCone p} := by
  have sign (g : G) (b : Bool) : IsClopen {p : G → Bool | p g = b} :=
    (isClopen_discrete {b}).preimage (continuous_apply g)
  simp_rw [isBiOrderCone_iff, Set.ofPred_and, Set.ofPred_forall]
  refine (sign 1 false).isClosed.inter ((isClosed_iInter fun g => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply g⁻¹)
      ((continuous_of_discreteTopology (f := Bool.not)).comp (continuous_apply g))).inter ?_)
  refine (isClosed_iInter fun a => isClosed_iInter fun b => ?_).inter
    (isClosed_iInter fun g => isClosed_iInter fun x => ?_)
  · exact isClosed_imp (sign a true).isOpen
      (isClosed_imp (sign b true).isOpen (sign (a * b) true).isClosed)
  · exact isClosed_imp (sign x true).isOpen (sign (g * x * g⁻¹) true).isClosed

instance : CompactSpace (BiOrdering G) :=
  isCompact_iff_compactSpace.mp isClosed_isBiOrderCone.isCompact

/-- The Sikora topology is Hausdorff and totally disconnected. -/
@[category API, AMS 54]
theorem separation : T2Space (BiOrdering G) ∧ TotallyDisconnectedSpace (BiOrdering G) :=
  ⟨inferInstance, inferInstance⟩

/-- The trivial group has a single bi-order, whose positive cone is empty. -/
@[category test, AMS 6 20]
theorem unique_punit : Nonempty (Unique (BiOrdering PUnit)) := by
  refine ⟨⟨⟨⟨fun _ => false, by constructor <;> simp⟩⟩, fun P => ?_⟩⟩
  exact Subtype.ext (funext fun g => by cases g; exact P.property.one)

/-- A positive element has positive powers of every positive exponent. -/
@[category API, AMS 6 20]
theorem pos_pow_succ (P : BiOrdering G) {g : G} (hg : P.val g = true) (n : ℕ) :
    P.val (g ^ (n + 1)) = true := by
  induction n with
  | zero => simpa using hg
  | succ n ih => simpa only [pow_succ _ (n + 1)] using P.property.mul _ _ ih hg

/-- Taking a positive power preserves the sign of every group element. -/
@[category API, AMS 6 20]
theorem sign_pow_succ (P : BiOrdering G) (g : G) (n : ℕ) :
    P.val (g ^ (n + 1)) = P.val g := by
  by_cases hg : g = 1
  · simp [hg]
  cases h : P.val g with
  | true => exact P.pos_pow_succ h n
  | false =>
    have hi : P.val g⁻¹ = true := by simp [P.property.inv g hg, h]
    have hn : P.val (g ^ (n + 1))⁻¹ = true := by simpa using P.pos_pow_succ hi n
    by_cases hpow : g ^ (n + 1) = 1
    · simp [hpow, P.property.one]
    · simpa [P.property.inv _ hpow] using hn

/-- The two orientations of the infinite cyclic group, indexed by the sign of its generator. -/
def intOrder (b : Bool) : BiOrdering (Multiplicative ℤ) :=
  ⟨fun x => if b then decide (0 < x.toAdd) else decide (x.toAdd < 0), by
    constructor
    · cases b <;> decide
    · intro x hx
      change x.toAdd ≠ 0 at hx
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true, toAdd_inv,
        ← decide_not, decide_eq_decide] <;> omega
    · intro x y
      cases b <;> simp <;> omega
    · intro g x
      simp [mul_comm g x]⟩

/-- Evaluating the cone at the generator identifies the bi-orders of the integers
with the two possible signs. -/
def intEquivBool : BiOrdering (Multiplicative ℤ) ≃ Bool where
  toFun P := P.val (Multiplicative.ofAdd 1)
  invFun := intOrder
  right_inv b := by cases b <;> rfl
  left_inv P := by
    let g := Multiplicative.ofAdd (1 : ℤ)
    let Q := intOrder (P.val g)
    have h : Q.val g = P.val g := by change (if P.val g then true else false) = _; simp
    have hi : Q.val g⁻¹ = P.val g⁻¹ := by
      rw [Q.property.inv _ (by decide : g ≠ 1), P.property.inv _ (by decide : g ≠ 1), h]
    apply Subtype.ext
    funext x
    change Q.val x = P.val x
    obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective x
    cases z with
    | ofNat n =>
      cases n with
      | zero => exact Q.property.one.trans P.property.one.symm
      | succ n =>
        have hx : Multiplicative.ofAdd (Int.ofNat (n + 1)) = g ^ (n + 1) := by
          apply Multiplicative.toAdd.injective
          simp [g]
        rw [hx, Q.sign_pow_succ, P.sign_pow_succ, h]
    | negSucc n =>
      have hx : Multiplicative.ofAdd (Int.negSucc n) = g⁻¹ ^ (n + 1) := by
        apply Multiplicative.toAdd.injective
        simp [g, Int.negSucc_eq]
      rw [hx, Q.sign_pow_succ, P.sign_pow_succ, hi]

/-- The infinite cyclic group has exactly two bi-orders. -/
@[category test, AMS 6 20]
theorem card_int : Nat.card (BiOrdering (Multiplicative ℤ)) = 2 := by
  rw [Nat.card_congr intEquivBool, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- The nonidentity element of the cyclic group of order two is its own inverse,
so neither choice of sign can define a bi-order. -/
@[category test, AMS 6 20]
theorem isEmpty_zmod_two : IsEmpty (BiOrdering (Multiplicative (ZMod 2))) := by
  refine ⟨fun P => ?_⟩
  let g := Multiplicative.ofAdd (1 : ZMod 2)
  have h := P.property.inv g (by decide : g ≠ 1)
  rw [show g⁻¹ = g by decide] at h
  cases hg : P.val g <;> simp [hg] at h

end BiOrdering

/-- The free metabelian group on a set of generators, obtained by killing the second
derived subgroup of the free group. -/
abbrev FreeMetabelianGroup (α : Type*) := FreeGroup α ⧸ derivedSeries (FreeGroup α) 2

/-- The free metabelian group has derived length at most two. -/
@[category API, AMS 20]
theorem derivedSeries_two (α : Type*) : derivedSeries (FreeMetabelianGroup α) 2 = ⊥ := by
  let N := derivedSeries (FreeGroup α) 2
  exact (map_derivedSeries_eq (QuotientGroup.mk'_surjective N) 2).symm.trans
    (QuotientGroup.map_mk'_self N)

/-- In rank one the free metabelian group is abelian. -/
@[category test, AMS 20]
theorem rank_one_mul_comm (x y : FreeMetabelianGroup (Fin 1)) : x * y = y * x := by
  let N := derivedSeries (FreeGroup (Fin 1)) 2
  have : IsCyclic (FreeMetabelianGroup (Fin 1)) :=
    isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  exact mul_comm' x y

/-- A Cantor space is a space homeomorphic to the countable product of discrete two-point spaces. -/
def IsCantorSpace (X : Type*) [TopologicalSpace X] : Prop := Nonempty (X ≃ₜ (ℕ → Bool))

/-- In rank one the group is infinite cyclic, whose two orders cannot form a Cantor space. -/
@[category test, AMS 6 20 54]
theorem not_isCantorSpace_int : ¬ IsCantorSpace (BiOrdering (Multiplicative ℤ)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  simp [BiOrdering.card_int] at h

/-- Is the space of bi-orderings of a free metabelian group of finite rank $n \ge 2$
homeomorphic to the Cantor set? Wang answered this in Corollary 7.6. -/
@[category research solved, question, AMS 6 20]
theorem kourovka_1_54 :
    ∀ n : ℕ, 2 ≤ n → IsCantorSpace (BiOrdering (FreeMetabelianGroup (Fin n))) := by
  sorry

/-- In every bi-order on the rank-two free metabelian group, every element strictly
between two elements of the derived subgroup lies in the derived subgroup (Wang, Theorem 6.2). -/
@[category research solved, AMS 6 20]
theorem kourovka_1_54.variants.rank_two_derived_convex
    (P : BiOrdering (FreeMetabelianGroup (Fin 2))) :
    ∀ a b c, a ∈ commutator _ → c ∈ commutator _ → P.lt a b → P.lt b c →
      b ∈ commutator _ := by
  sorry

end Kourovka.«1.54»

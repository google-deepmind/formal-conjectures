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

public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Steiner triple systems

A Steiner triple system is a block design with parameters $t = 2$ and $k = 3$.
This file gives the pair formulation, transport along equivalences, constructions from
Steiner quasigroups, Bose's and Skolem's constructions, and Kirkman's existence criterion.

*Reference:* Kwan, Sah, Sawhney, and Simkin, _High-girth Steiner triple systems_,
[arXiv:2201.04554v4, pp. 1–2](https://arxiv.org/pdf/2201.04554v4).
-/

@[expose] public section

namespace Finset

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- A Steiner triple system on the ground vertex type is a $2$-$(v,3,1)$ block design. -/
abbrev IsSteinerTripleSystem (H : Finset (Finset V)) : Prop := H.IsBlockDesign 2 3

/-- The block-design definition is equivalent to unique coverage of pairs of distinct vertices. -/
theorem isSteinerTripleSystem_iff {H : Finset (Finset V)} :
    H.IsSteinerTripleSystem ↔
      (∀ e ∈ H, e.card = 3) ∧ ∀ x y : V, x ≠ y → ∃! e, e ∈ H ∧ x ∈ e ∧ y ∈ e := by
  constructor
  · rintro ⟨h3, hu⟩
    refine ⟨h3, fun x y hxy => ?_⟩
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff, and_assoc] using hu {x, y} (Finset.card_pair hxy)
  · rintro ⟨h3, hu⟩
    refine ⟨h3, fun S hS => ?_⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hS
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff, and_assoc] using hu x y hxy

omit [DecidableEq V] [DecidableEq W] in
/-- Every block of a Steiner triple system has three vertices. -/
theorem IsSteinerTripleSystem.card_triple {H : Finset (Finset V)}
    (hH : H.IsSteinerTripleSystem) (e : Finset V) (he : e ∈ H) : e.card = 3 := hH.1 e he

/-- Each pair of distinct ground vertices lies in exactly one triple. -/
theorem IsSteinerTripleSystem.existsUnique_triple {H : Finset (Finset V)}
    (hH : H.IsSteinerTripleSystem) (x y : V) (hxy : x ≠ y) :
    ∃! e, e ∈ H ∧ x ∈ e ∧ y ∈ e := (isSteinerTripleSystem_iff.1 hH).2 x y hxy

/-- A Steiner quasigroup on a finite type gives a Steiner triple system. -/
theorem isSteinerTripleSystem_of_op [Fintype V] (op : V → V → V) (idem : ∀ x, op x x = x)
    (comm : ∀ x y, op x y = op y x) (canc : ∀ x y, op x (op x y) = y) :
    IsSteinerTripleSystem
      ((Finset.univ.offDiag).image fun p : V × V => ({p.1, p.2, op p.1 p.2} : Finset V)) := by
  have hx : ∀ x y, x ≠ y → op x y ≠ x := fun x y hxy h => by
    have := canc x y; rw [h, idem] at this; exact hxy this
  have hy : ∀ x y, x ≠ y → op x y ≠ y := fun x y hxy h => by
    have := canc y x; rw [comm y x, h, idem] at this; exact hxy this.symm
  refine isSteinerTripleSystem_iff.2 ⟨?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_univ, true_and]
    rintro e ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.card_insert_of_notMem, Finset.card_pair (hy a b hab).symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, (hx a b hab).symm⟩
  · intro x y hxy
    refine ⟨{x, y, op x y}, ⟨?_, by simp, by simp⟩, ?_⟩
    · simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_univ, true_and]
      exact ⟨(x, y), hxy, rfl⟩
    · simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_univ, true_and]
      rintro e ⟨⟨⟨a, b⟩, hab, rfl⟩, hxe, hye⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe hye
      have h1 := canc a b
      have h2 := canc b a
      rw [comm b a] at h2
      have h3 := comm a (op a b)
      have h4 := comm b (op a b)
      rcases hxe with rfl | rfl | rfl <;> rcases hye with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hxy
        | (ext z; simp only [Finset.mem_insert, Finset.mem_singleton] <;> grind)

omit [DecidableEq V] in
/-- Steiner triple systems transfer along bijections of the vertex type. -/
theorem IsSteinerTripleSystem.map_equiv {H : Finset (Finset V)} (hH : IsSteinerTripleSystem H)
    (f : V ≃ W) : IsSteinerTripleSystem (H.image (Finset.map f.toEmbedding)) := by
  classical
  obtain ⟨h3, hu⟩ := isSteinerTripleSystem_iff.1 hH
  refine isSteinerTripleSystem_iff.2 ⟨?_, ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨e, he, rfl⟩
    simpa using h3 e he
  · intro x y hxy
    obtain ⟨e, ⟨he, hxe, hye⟩, huniq⟩ := hu (f.symm x) (f.symm y) (by simpa using hxy)
    refine ⟨e.map f.toEmbedding, ⟨Finset.mem_image_of_mem _ he, ?_, ?_⟩, ?_⟩
    · simpa [Finset.mem_map_equiv] using hxe
    · simpa [Finset.mem_map_equiv] using hye
    · rintro _ ⟨hd, hxd, hyd⟩
      obtain ⟨d, hdH, rfl⟩ := Finset.mem_image.1 hd
      rw [huniq d ⟨hdH, by simpa [Finset.mem_map_equiv] using hxd,
        by simpa [Finset.mem_map_equiv] using hyd⟩]

omit [DecidableEq V] in
/-- A Steiner triple system on a finite type with `n` elements gives one on `Fin n`. -/
theorem IsSteinerTripleSystem.exists_fin [Fintype V] {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) {n : ℕ} (hn : Fintype.card V = n) :
    ∃ H' : Finset (Finset (Fin n)), IsSteinerTripleSystem H' :=
  ⟨_, hH.map_equiv (Fintype.equivFinOfCardEq hn)⟩

/-- In a Steiner triple system two distinct edges share at most one vertex. -/
theorem IsSteinerTripleSystem.card_inter_le_one {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hef : e ≠ f) :
    (e ∩ f).card ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
  rw [Finset.mem_inter] at hx hy
  obtain ⟨_, _, huniq⟩ := hH.existsUnique_triple x y hxy
  exact hef ((huniq e ⟨he, hx.1, hy.1⟩).trans (huniq f ⟨hf, hx.2, hy.2⟩).symm)

end Finset

section

namespace Finset.Bose

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Bose's Steiner quasigroup on `R × ZMod 3`, where `c` is an inverse of `2` in `R`. -/
def op (c : R) : R × ZMod 3 → R × ZMod 3 → R × ZMod 3
  | (a, i), (b, j) =>
    if i = j then (if a = b then (a, i) else (c * (a + b), i + 1))
    else if a = b then (a, -i - j)
    else if j = i + 1 then (2 * b - a, i) else (2 * a - b, j)

lemma zmod3_aux₁ : ∀ i j : ZMod 3, j = i + 1 → i ≠ j + 1 := by decide
lemma zmod3_aux₂ : ∀ i j : ZMod 3, i ≠ j → j ≠ i + 1 → i = j + 1 := by decide
lemma zmod3_aux₃ : ∀ i j : ZMod 3, i ≠ j → i ≠ -i - j := by decide

lemma op_idem (c : R) (p : R × ZMod 3) : op c p p = p := by
  obtain ⟨a, i⟩ := p
  simp [op]

lemma op_comm (c : R) (p q : R × ZMod 3) : op c p q = op c q p := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  by_cases hij : i = j
  · subst hij
    by_cases hab : a = b
    · subst hab; rfl
    · simp [op, hab, Ne.symm hab, add_comm]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hab : a = b
    · subst hab
      simp only [op, hij, hji, ite_false, ite_true]
      congr 1; ring
    · have hba : b ≠ a := Ne.symm hab
      by_cases h1 : j = i + 1
      · have h2 := zmod3_aux₁ i j h1
        subst h1
        simp [op, hab, hba, h2]
      · have h2 := zmod3_aux₂ i j hij h1
        subst h2
        simp [op, hab, hba, h1]

section

variable {c : R} (hc : 2 * c = 1)
include hc

omit [DecidableEq R] in
lemma eq_of_two_mul_eq {a b : R} (h : 2 * a = 2 * b) : a = b := by
  have := congrArg (c * ·) h
  linear_combination this - (a - b) * hc

lemma op_canc (p q : R × ZMod 3) : op c p (op c p q) = q := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  by_cases hij : i = j
  · subst hij
    by_cases hab : a = b
    · subst hab; simp [op]
    · have hne : a ≠ c * (a + b) := fun h => hab (by linear_combination 2 * h + (a + b) * hc)
      simp [op, hab, hne]
      linear_combination (a + b) * hc
  · by_cases hab : a = b
    · subst hab
      simp [op, hij, zmod3_aux₃ i j hij]
    · have hne : 2 * b - a ≠ a := fun h => hab (by linear_combination -c * h + (b - a) * hc)
      have hne' : a ≠ 2 * a - b := fun h => hab (by linear_combination -h)
      by_cases h1 : j = i + 1
      · subst h1
        simp only [op, hij, ite_false, hab, ite_true, Ne.symm hne]
        ext
        · simp only; linear_combination b * hc
        · rfl
      · have h2 := zmod3_aux₂ i j hij h1
        subst h2
        simp [op, hab, h1, hne']

theorem isSteinerTripleSystem [Fintype R] :
    IsSteinerTripleSystem ((Finset.univ.offDiag).image
      fun p : (R × ZMod 3) × (R × ZMod 3) => ({p.1, p.2, op c p.1 p.2} : Finset (R × ZMod 3)))
      :=
  isSteinerTripleSystem_of_op _ (op_idem c) (op_comm c) (op_canc hc)

end

/-- **Bose's construction**: there is a Steiner triple system on `6 k + 3` points. -/
theorem exists_isSteinerTripleSystem (k : ℕ) :
    ∃ H : Finset (Finset (Fin (6 * k + 3))), IsSteinerTripleSystem H := by
  have hc : 2 * ((k + 1 : ℕ) : ZMod (2 * k + 1)) = 1 := by
    have h0 : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination h0
  refine (isSteinerTripleSystem hc).exists_fin ?_
  simp [ZMod.card]
  ring

end Finset.Bose

end


/-!
## Skolem's construction of Steiner triple systems of order `6k + 1`

We work with an abelian group `Q` of order `2k` together with an element `κ` of order `2` and
a bijection `r : Q ≃ Q` such that `x ∘ y := r (x + y)` is *half-idempotent*, i.e. `x ∘ x ∈ {x, x + κ}`.
Skolem's triples on `{∞} ∪ Q × ZMod 3` are then encoded by a Steiner quasigroup `op`.
-/

section

namespace Finset.Skolem

variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]

/-- Auxiliary function for `op`: the third point of the triple through `(x, i)` and `(y, i + 1)`. -/
def third (r : Q ≃ Q) (x y : Q) (i : ZMod 3) : Option (Q × ZMod 3) :=
  if r (x + x) = y then (if r (x + x) = x then some (x, i + 2) else none)
  else some (r.symm y - x, i)

/-- Skolem's Steiner quasigroup on `Option (Q × ZMod 3)` (`none` is the point at infinity). -/
def op (κ : Q) (r : Q ≃ Q) : Option (Q × ZMod 3) → Option (Q × ZMod 3) → Option (Q × ZMod 3)
  | none, none => none
  | none, some (x, i) => some (x + κ, if r (x + x) = x then i - 1 else i + 1)
  | some (x, i), none => some (x + κ, if r (x + x) = x then i - 1 else i + 1)
  | some (x, i), some (y, j) =>
    if i = j then (if x = y then some (x, i) else some (r (x + y), i + 1))
    else if j = i + 1 then third r x y i else third r y x j

lemma zmod3_aux₁ : ∀ i j : ZMod 3, j = i + 1 → i ≠ j + 1 := by decide
lemma zmod3_aux₂ : ∀ i j : ZMod 3, i ≠ j → j ≠ i + 1 → i = j + 1 := by decide

lemma op_idem (κ : Q) (r : Q ≃ Q) (p : Option (Q × ZMod 3)) : op κ r p p = p := by
  rcases p with _ | ⟨x, i⟩ <;> simp [op]

lemma op_comm (κ : Q) (r : Q ≃ Q) (p q : Option (Q × ZMod 3)) : op κ r p q = op κ r q p := by
  rcases p with _ | ⟨x, i⟩ <;> rcases q with _ | ⟨y, j⟩
  · rfl
  · rfl
  · rfl
  · by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; rfl
      · simp [op, hxy, Ne.symm hxy, add_comm]
    · by_cases h1 : j = i + 1
      · subst h1
        simp [op, zmod3_aux₁ i _ rfl]
      · have h2 := zmod3_aux₂ i j hij h1
        subst h2
        simp [op, h1]

section

variable {κ : Q} {r : Q ≃ Q} (hκ : κ + κ = 0) (hκ0 : κ ≠ 0)
  (hd : ∀ x, r (x + x) = x ∨ r (x + x) = x + κ)
include hκ hκ0 hd

omit [DecidableEq Q] hκ0 hd in
lemma add_κ_add_κ (x : Q) : x + κ + κ = x := by
  rw [add_assoc, hκ, add_zero]

omit [DecidableEq Q] hκ0 hd in
lemma d_add_κ (x : Q) : r (x + κ + (x + κ)) = r (x + x) := by
  congr 1
  rw [add_add_add_comm, hκ, add_zero]

omit [DecidableEq Q] hκ hd in
lemma ne_add_κ (x : Q) : x ≠ x + κ := fun h => hκ0 (by simpa using h)

omit [DecidableEq Q] in
lemma base_add_κ (x : Q) : r (x + κ + (x + κ)) = x + κ ↔ r (x + x) ≠ x := by
  rw [d_add_κ hκ]
  constructor
  · intro h h'
    exact ne_add_κ hκ0 x (h'.symm.trans h)
  · intro h
    exact (hd x).resolve_left h

lemma op_canc (p q : Option (Q × ZMod 3)) : op κ r p (op κ r p q) = q := by
  rcases p with _ | ⟨x, i⟩ <;> rcases q with _ | ⟨y, j⟩
  · rfl
  · -- `p = ∞`
    by_cases hb : r (y + y) = y
    · have : ¬ r (y + κ + (y + κ)) = y + κ := fun h => (base_add_κ hκ hκ0 hd y).1 h hb
      simp [op, hb, this, add_κ_add_κ hκ]
    · have : r (y + κ + (y + κ)) = y + κ := (base_add_κ hκ hκ0 hd y).2 hb
      simp [op, hb, this, add_κ_add_κ hκ]
  · -- `q = ∞`
    by_cases hb : r (x + x) = x
    · have hl : ¬ (i - 1 = i + 1) := by revert i; decide
      have hl' : ¬ (i = i - 1) := by revert i; decide
      simp [op, third, hb, hκ0, hl, hl', d_add_κ hκ]
    · have hb' := (hd x).resolve_left hb
      have hl : ¬ (i = i + 1) := by revert i; decide
      simp [op, third, hb', hκ0, hl]
  · by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; simp [op]
      · have hne : r (x + x) ≠ r (x + y) := fun h => hxy (add_left_cancel (r.injective h))
        have hl : ¬ (i = i + 1) := by revert i; decide
        simp [op, third, hxy, hne, hl]
    · by_cases h1 : j = i + 1
      · subst h1
        by_cases hdy : r (x + x) = y
        · by_cases hb : r (x + x) = x
          · subst hdy
            have hl : ¬ (i = i + 2) := by revert i; decide
            have hl' : ¬ (i + 2 = i + 1) := by revert i; decide
            have hl'' : i + 2 + 2 = i + 1 := by revert i; decide
            simp [op, third, hb, hl, hl', hl'']
          · have hy : x + κ = y := ((hd x).resolve_left hb).symm.trans hdy
            have hyx : y ≠ x := hdy ▸ hb
            simp [op, third, hdy, hyx, hy]
        · have hv : x ≠ r.symm y - x := fun h => hdy (by
            conv_lhs => rw [show x + x = x + (r.symm y - x) by rw [← h]]
            simp)
          simp [op, third, hdy, hv]
      · have h2 := zmod3_aux₂ i j hij h1
        subst h2
        have hl : ¬ (j + 1 = j) := by revert j; decide
        have hl' : ¬ (j = j + 1 + 1) := by revert j; decide
        by_cases hdy : r (y + y) = x
        · by_cases hb : r (y + y) = y
          · have hxy : x = y := hdy.symm.trans hb
            subst hxy
            have hl₁ : ¬ (j + 1 = j + 2) := by revert j; decide
            have hl₂ : j + 2 = j + 1 + 1 := by revert j; decide
            have hl₃ : j + 1 + 2 = j := by revert j; decide
            simp [op, third, hb, hl, hl', hl₂, hl₃]
          · have hx : y + κ = x := ((hd y).resolve_left hb).symm.trans hdy
            subst hx
            have hbx : r (y + κ + (y + κ)) = y + κ := by rw [d_add_κ hκ]; exact hdy
            simp [op, third, hl, hl', hdy, hκ0, hbx, add_κ_add_κ hκ]
        · have hv : r ((r.symm x - y) + (r.symm x - y)) ≠ x := fun h => hdy (by
            have h' : r.symm x - y + (r.symm x - y) = r.symm x - y + y := by
              apply r.injective; rw [h]; simp
            have : r.symm x - y = y := add_left_cancel h'
            rw [this] at h
            exact h)
          simp [op, third, hl, hl', hdy, hv]


theorem isSteinerTripleSystem [Fintype Q] :
    IsSteinerTripleSystem ((Finset.univ.offDiag).image
      fun p : Option (Q × ZMod 3) × Option (Q × ZMod 3) =>
        ({p.1, p.2, op κ r p.1 p.2} : Finset (Option (Q × ZMod 3)))) :=
  isSteinerTripleSystem_of_op _ (op_idem κ r) (op_comm κ r) (op_canc hκ hκ0 hd)

end

/-- The bijection `ZMod (2k) → ZMod (2k)` sending `2a ↦ a` and `2a + 1 ↦ a + k` (`0 ≤ a < k`),
so that `x ∘ y := r (x + y)` is a half-idempotent commutative quasigroup. -/
def rFun (k : ℕ) (s : ZMod (2 * k)) : ZMod (2 * k) :=
  ((s.val / 2 + k * (s.val % 2) : ℕ) : ZMod (2 * k))

lemma rFun_val {k : ℕ} (hk : 0 < k) (s : ZMod (2 * k)) :
    (rFun k s).val = s.val / 2 + k * (s.val % 2) := by
  have : NeZero (2 * k) := ⟨by omega⟩
  have hs := ZMod.val_lt s
  unfold rFun
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> rw [h] <;> omega

lemma rFun_injective {k : ℕ} (hk : 0 < k) : Function.Injective (rFun k) := by
  have : NeZero (2 * k) := ⟨by omega⟩
  intro s t hst
  have h := congrArg ZMod.val hst
  rw [rFun_val hk, rFun_val hk] at h
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  apply ZMod.val_injective
  rcases Nat.mod_two_eq_zero_or_one s.val with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one t.val with h2 | h2 <;> rw [h1, h2] at h <;> omega

lemma rFun_add_self {k : ℕ} (hk : 0 < k) (x : ZMod (2 * k)) :
    rFun k (x + x) = x ∨ rFun k (x + x) = x + k := by
  have : NeZero (2 * k) := ⟨by omega⟩
  have hx := ZMod.val_lt x
  have hxx : (x + x).val = (x.val + x.val) % (2 * k) := ZMod.val_add x x
  by_cases hlt : x.val < k
  · left
    apply ZMod.val_injective
    rw [rFun_val hk, hxx, Nat.mod_eq_of_lt (by omega)]
    have : (x.val + x.val) % 2 = 0 := by omega
    rw [this]; omega
  · right
    apply ZMod.val_injective
    rw [rFun_val hk, hxx, ZMod.val_add, ZMod.val_natCast_of_lt (by omega : k < 2 * k)]
    have h1 : (x.val + x.val) % (2 * k) = x.val + x.val - 2 * k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have h2 : (x.val + k) % (2 * k) = x.val - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [h1, h2]
    have : (x.val + x.val - 2 * k) % 2 = 0 := by omega
    rw [this]; omega

/-- **Skolem's construction**: there is a Steiner triple system on `6 k + 1` points. -/
theorem exists_isSteinerTripleSystem (k : ℕ) :
    ∃ H : Finset (Finset (Fin (6 * k + 1))), IsSteinerTripleSystem H := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨∅, isSteinerTripleSystem_iff.2 ⟨by simp, fun x y hxy => absurd (Fin.ext ?_) hxy⟩⟩
    have := x.isLt
    have := y.isLt
    omega
  have : NeZero (2 * k) := ⟨by omega⟩
  let r : ZMod (2 * k) ≃ ZMod (2 * k) :=
    Equiv.ofBijective _ (rFun_injective hk).bijective_of_finite
  have hκ : (k : ZMod (2 * k)) + k = 0 := by
    have := ZMod.natCast_self (2 * k)
    push_cast at this
    linear_combination this
  have hκ0 : (k : ZMod (2 * k)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hk h
    omega
  refine (isSteinerTripleSystem (r := r) hκ hκ0 (rFun_add_self hk)).exists_fin ?_
  simp [ZMod.card]
  ring

end Finset.Skolem

end


/-!
## Kirkman's theorem

A Steiner triple system on `n ≥ 1` points exists if and only if `n ≡ 1, 3 (mod 6)`.

* Necessity is the usual double-counting argument: every point lies on `(n - 1) / 2` triples
  and there are `n (n - 1) / 6` triples.
* Sufficiency follows from Bose's (`n = 6k + 3`) and Skolem's (`n = 6k + 1`) constructions.
-/

section

namespace Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- In a Steiner triple system on `n` points every point lies on exactly `(n - 1) / 2` edges;
in particular `n - 1 = 2 * deg v`. -/
theorem IsSteinerTripleSystem.card_sub_one_eq {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) (v : V) :
    Fintype.card V - 1 = 2 * (H.filter (v ∈ ·)).card := by
  have hcover : Finset.univ.erase v = (H.filter (v ∈ ·)).biUnion (fun e => e.erase v) := by
    ext w
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
      Finset.mem_filter]
    constructor
    · intro hw
      obtain ⟨e, ⟨he, hve, hwe⟩, -⟩ := hH.existsUnique_triple v w (Ne.symm hw)
      exact ⟨e, ⟨he, hve⟩, hw, hwe⟩
    · rintro ⟨e, -, hw, -⟩
      exact hw
  have hdisj : ∀ e ∈ H.filter (v ∈ ·), ∀ f ∈ H.filter (v ∈ ·), e ≠ f →
      Disjoint (e.erase v) (f.erase v) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro w hwe hwf
    rw [Finset.mem_filter] at he hf
    rw [Finset.mem_erase] at hwe hwf
    obtain ⟨_, _, huniq⟩ := hH.existsUnique_triple v w (Ne.symm hwe.1)
    exact hef ((huniq e ⟨he.1, he.2, hwe.2⟩).trans (huniq f ⟨hf.1, hf.2, hwf.2⟩).symm)
  have h := congrArg Finset.card hcover
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
    Finset.card_biUnion hdisj] at h
  rw [h, Finset.sum_const_nat (m := 2), mul_comm]
  intro e he
  rw [Finset.mem_filter] at he
  rw [Finset.card_erase_of_mem he.2, hH.card_triple e he.1]

/-- In a Steiner triple system on `n` points there are exactly `n.choose 2 / 3` edges. -/
theorem IsSteinerTripleSystem.choose_two_eq {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) : (Fintype.card V).choose 2 = 3 * H.card := by
  have hcover : Finset.univ.powersetCard 2 = H.biUnion (fun e => e.powersetCard 2) := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hs
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
      obtain ⟨e, ⟨he, hxe, hye⟩, -⟩ := hH.existsUnique_triple x y hxy
      refine ⟨e, he, ?_, hs⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rintro ⟨e, -, -, hs⟩
      exact hs
  have hdisj : ∀ e ∈ H, ∀ f ∈ H, e ≠ f →
      Disjoint (e.powersetCard 2) (f.powersetCard 2) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro s hse hsf
    rw [Finset.mem_powersetCard] at hse hsf
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hse.2
    obtain ⟨_, _, huniq⟩ := hH.existsUnique_triple x y hxy
    have hx : x ∈ ({x, y} : Finset V) := by simp
    have hy : y ∈ ({x, y} : Finset V) := by simp
    exact hef ((huniq e ⟨he, hse.1 hx, hse.1 hy⟩).trans (huniq f ⟨hf, hsf.1 hx, hsf.1 hy⟩).symm)
  have h := congrArg Finset.card hcover
  rw [Finset.card_powersetCard, Finset.card_univ, Finset.card_biUnion hdisj] at h
  rw [h, Finset.sum_const_nat (m := 3), mul_comm]
  intro e he
  rw [Finset.card_powersetCard, hH.card_triple e he]
  rfl

/-- **Necessary condition**: if there is a Steiner triple system on `n ≥ 1` points, then
`n ≡ 1, 3 (mod 6)`. -/
theorem IsSteinerTripleSystem.card_mod_six {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) (hV : Nonempty V) :
    Fintype.card V % 6 = 1 ∨ Fintype.card V % 6 = 3 := by
  obtain ⟨v⟩ := hV
  have h1 := hH.card_sub_one_eq v
  have h2 := hH.choose_two_eq
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  set n := Fintype.card V
  set d := (H.filter (v ∈ ·)).card
  have hn : n = 2 * d + 1 := by omega
  rw [Nat.choose_two_right, hn, Nat.add_sub_cancel,
    show (2 * d + 1) * (2 * d) = 2 * ((2 * d + 1) * d) by ring,
    Nat.mul_div_cancel_left _ two_pos] at h2
  have h3 : (2 * d + 1) * d % 3 = 0 := by omega
  rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod] at h3
  have : d % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hd : d % 3 <;> simp_all <;> omega

/-- **Kirkman's theorem**: for `n ≥ 1` there is a Steiner triple system on `n` points if and only
if `n ≡ 1, 3 (mod 6)`. -/
theorem exists_isSteinerTripleSystem_iff {n : ℕ} (hn : 1 ≤ n) :
    (∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H) ↔ (n % 6 = 1 ∨ n % 6 = 3) := by
  constructor
  · rintro ⟨H, hH⟩
    simpa using hH.card_mod_six ⟨⟨0, hn⟩⟩
  · rintro (h | h)
    · obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 1 := ⟨n / 6, by omega⟩
      exact Skolem.exists_isSteinerTripleSystem k
    · obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 3 := ⟨n / 6, by omega⟩
      exact Bose.exists_isSteinerTripleSystem k

end Finset

end

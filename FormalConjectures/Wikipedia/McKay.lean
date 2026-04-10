import Mathlib

/-!
# The McKay Conjecture (now Theorem)

We formalize the definitions of characters and irreducible characters of finite groups,
and state the McKay conjecture: for a finite group `G`, a prime `p`, and a Sylow
`p`-subgroup `P` of `G`, the number of irreducible complex characters of `G` with
degree coprime to `p` equals the corresponding number for the normalizer `N_G(P)`.

## Main Definitions

* `FDRep.character` (from Mathlib): The character of a finite-dimensional representation
  `ρ : G → GL(V)`, defined as `χ_ρ(g) = Tr(ρ(g))`.

* `Representation.IsIrreducible` (from Mathlib): A representation is irreducible if the
  underlying module is simple (has no proper nonzero subrepresentations).

* `IrrCharIsoClass`: The type of isomorphism classes of irreducible (simple)
  finite-dimensional complex representations of a finite group `G`. This formalizes
  `Irr(G)`.

* `IrrCharIsoClass.degree`: The degree of an irreducible character, defined as the
  dimension of the underlying representation. This is well-defined on isomorphism classes
  since isomorphic representations have the same dimension. In characteristic 0, the
  degree equals `χ(1)`.

* `IrrPPrime`: The set `Irr_{p'}(G)` of isomorphism classes of irreducible complex
  characters whose degree is not divisible by a prime `p`.

## Main Statement

* `mckay_conjecture`: For a prime `p`, a finite group `G`, and a Sylow `p`-subgroup `P`,
  `|Irr_{p'}(G)| = |Irr_{p'}(N_G(P))|`.

## Verified Examples

We verify the McKay conjecture in the following cases:

* **Groups with normal Sylow subgroups** (`mckay_of_normal_sylow`): When `P` is normal
  in `G`, we have `N_G(P) = G`, so both sides are trivially equal.

* **Abelian groups** (`mckay_comm_group`): All subgroups of an abelian group are normal,
  so the above applies.

* **Cyclic groups of prime order** (`mckay_cyclic_prime`): `Multiplicative (ZMod p)` for
  prime `p`, as an instance of the abelian case.

* **Symmetric group S₃ for p = 3** (`mckay_S3_p3`): The Sylow 3-subgroup of S₃ is
  normal (it is the unique subgroup of order 3), so both sides are equal.

* **Dihedral group D₃ for p = 3** (`mckay_D3_p3`): The dihedral group of order 6 has
  a normal Sylow 3-subgroup.
-/

noncomputable section

open CategoryTheory Classical

universe u

/-! ### Character of a representation -/

section CharacterDef

variable {k : Type u} [Field k] {G : Type u} [Monoid G] (V : FDRep k G)

/-- The character of a representation, `χ_ρ(g) = Tr(ρ(g))`.
This is `FDRep.character` from Mathlib. -/
example (g : G) : k := V.character g

/-- In characteristic 0, the character evaluated at the identity equals the
dimension of the representation. -/
example [CharZero k] : V.character 1 = (Module.finrank k V : k) :=
  FDRep.char_one V

end CharacterDef

/-! ### Irreducible characters and Irr(G) -/

section IrrDef

variable (G : Type) [Group G] [Fintype G]

/-- The setoid on simple (irreducible) `FDRep ℂ G` given by categorical isomorphism. -/
instance simpleRepIsoSetoid : Setoid { V : FDRep ℂ G // Simple V } where
  r := fun V W => Nonempty (V.1 ≅ W.1)
  iseqv :=
    ⟨fun _ => ⟨Iso.refl _⟩,
     fun ⟨h⟩ => ⟨h.symm⟩,
     fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩⟩

/-- `IrrCharIsoClass G` is the type of isomorphism classes of irreducible (simple)
finite-dimensional complex representations of `G`. This formalizes `Irr(G)`. -/
def IrrCharIsoClass := Quotient (simpleRepIsoSetoid G)

/-- The degree of an irreducible character, defined as the dimension of the underlying
representation. -/
def IrrCharIsoClass.degree : IrrCharIsoClass G → ℕ :=
  Quotient.lift
    (fun V : { V : FDRep ℂ G // Simple V } => Module.finrank ℂ V.1)
    (fun _ _ ⟨h⟩ => LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv h))

end IrrDef

/-! ### The set Irr_{p'}(G) -/

section IrrPPrime

variable (G : Type) [Group G] [Fintype G] (p : ℕ)

/-- `IrrPPrime G p` is the set of isomorphism classes of irreducible complex characters
of `G` whose degree is not divisible by `p`. This formalizes `Irr_{p'}(G)`. -/
def IrrPPrime : Set (IrrCharIsoClass G) :=
  { χ | ¬(p ∣ IrrCharIsoClass.degree G χ) }

end IrrPPrime

/-! ### The McKay Conjecture -/

/-- **The McKay Conjecture.** Let `p` be a prime, `G` a finite group, and `P` a Sylow
`p`-subgroup of `G`. Then the number of irreducible complex characters of `G` with
degree not divisible by `p` equals the number of such characters of the normalizer
`N_G(P)`. -/
theorem mckay_conjecture
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [Group G] [Fintype G]
    (P : Sylow p G) :
    Nat.card (IrrPPrime G p) =
      Nat.card (IrrPPrime ((P : Subgroup G).normalizer) p) := by
  sorry

/-! ## Transfer of representations along group isomorphisms -/

section Transfer

variable {G : Type} [Group G] [Fintype G]
         {H : Type} [Group H] [Fintype H]

/-- A group isomorphism induces a categorical equivalence of representation categories. -/
def fdrepEquivOfMulEquiv (e : G ≃* H) : (FDRep ℂ G) ≌ (FDRep ℂ H) :=
  (Action.resEquiv (FGModuleCat ℂ) e).symm

/-- An equivalence of categories preserves simple (irreducible) objects. -/
lemma simple_of_equiv {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ≌ D) (X : C) [Simple X] : Simple (F.functor.obj X) := by
  refine' { .. };
  intro Y f hf
  constructor
  · intro h_iso
    cases' h_iso with g hg;
    cases' g with g hg;
    intro h; replace hg := congr_arg ( fun f => F.inverse.map f ) hg.2; simp_all +decide ;
    rw [ eq_comm ] at hg;
    have := F.unitIso.app X;
    cases' this with h₁ h₂ h₃ h₄;
    have := h₃ ▸ Category.assoc h₁ h₂ h₁; simp_all +decide ;
    exact absurd h₃.symm ( by exact id_nonzero X )
  · intro h_nonzero
    have hg_iso : IsIso (F.inverse.map f) := by
      have hg_mono : Mono (F.inverse.map f) := by
        exact Functor.map_mono F.inverse f
      have hg_nonzero : F.inverse.map f ≠ 0 := by
        intro h_zero;
        apply_fun F.functor.map at h_zero ; simp_all +decide [ CategoryTheory.Functor.map_zero ];
        have h_counit_iso : IsIso (F.counit.app Y) ∧ IsIso (F.counitInv.app (F.functor.obj X)) := by
          exact ⟨ by exact NatIso.hom_app_isIso F.counitIso Y,
                   by exact NatIso.inv_app_isIso F.counitIso (F.functor.obj X) ⟩;
        cases' h_counit_iso with h₁ h₂;
        exact h_nonzero ( by simpa [ h₁, h₂ ] using congr_arg ( fun g => CategoryTheory.inv ( F.counit.app Y ) ≫ g ≫ CategoryTheory.inv ( F.counitInv.app ( F.functor.obj X ) ) ) h_zero )
      have hg_simple : Simple (F.inverse.obj (F.functor.obj X)) := by
        have hg_iso : F.inverse.obj (F.functor.obj X) ≅ X :=
          F.unitIso.app X |> CategoryTheory.Iso.symm
        exact (Simple.iff_of_iso hg_iso.symm).mp inferInstance
      exact (Simple.mono_isIso_iff_nonzero (F.inverse.map f)).mpr hg_nonzero
    have := F.functor.map_isIso ( F.inverse.map f ) ; aesop

/-- An equivalence of categories reflects simple (irreducible) objects. -/
lemma simple_of_equiv_inverse {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ≌ D) (Y : D) [Simple Y] : Simple (F.inverse.obj Y) := by
  convert simple_of_equiv F.symm Y using 1

/-- A group isomorphism induces a map on simple representations (as subtypes). -/
def mapSimpleRep (e : G ≃* H)
    (V : { V : FDRep ℂ G // Simple V }) :
    { W : FDRep ℂ H // Simple W } :=
  ⟨(fdrepEquivOfMulEquiv e).functor.obj V.1,
   @simple_of_equiv _ _ _ _ _ _ (fdrepEquivOfMulEquiv e) V.1 V.2⟩

/-- The map on simple representations respects isomorphism. -/
lemma mapSimpleRep_respects_iso (e : G ≃* H)
    (V W : { V : FDRep ℂ G // Simple V }) (h : Nonempty (V.1 ≅ W.1)) :
    Nonempty ((mapSimpleRep e V).1 ≅ (mapSimpleRep e W).1) :=
  ⟨(fdrepEquivOfMulEquiv e).functor.mapIso h.some⟩

/-- A group isomorphism induces a map on `IrrCharIsoClass`. -/
def IrrCharIsoClass.map (e : G ≃* H) :
    IrrCharIsoClass G → IrrCharIsoClass H :=
  Quotient.lift
    (fun V => ⟦mapSimpleRep e V⟧)
    (fun V W h => Quotient.sound (mapSimpleRep_respects_iso e V W h))

/-- A group isomorphism induces a bijection on `IrrCharIsoClass`. -/
def IrrCharIsoClass.mapEquiv (e : G ≃* H) :
    IrrCharIsoClass G ≃ IrrCharIsoClass H where
  toFun := IrrCharIsoClass.map e
  invFun := IrrCharIsoClass.map e.symm
  left_inv := by
    intro χ;
    obtain ⟨ V, hV ⟩ := Quotient.exists_rep χ;
    rw [ ← hV ];
    convert Quotient.sound _;
    unfold mapSimpleRep;
    unfold fdrepEquivOfMulEquiv;
    simp +decide [ Action.res ];
    simp +decide [ MonoidHom.comp_assoc ]
  right_inv := by
    intro χ;
    obtain ⟨ V, hV ⟩ := Quotient.exists_rep χ;
    rw [ ← hV ];
    convert Quotient.sound _;
    unfold mapSimpleRep;
    unfold fdrepEquivOfMulEquiv;
    simp +decide [ Action.res ];
    simp +decide [ MonoidHom.comp_assoc ]

/-- The bijection induced by a group isomorphism preserves the degree. -/
lemma IrrCharIsoClass.mapEquiv_degree (e : G ≃* H) (χ : IrrCharIsoClass G) :
    IrrCharIsoClass.degree H (IrrCharIsoClass.mapEquiv e χ) =
    IrrCharIsoClass.degree G χ := by
  induction χ using Quotient.inductionOn';
  aesop

/-- A group isomorphism induces an equivalence on `IrrPPrime`. -/
def IrrPPrime.equivOfMulEquiv (e : G ≃* H) (p : ℕ) :
    IrrPPrime G p ≃ IrrPPrime H p where
  toFun := fun ⟨χ, hχ⟩ => ⟨IrrCharIsoClass.mapEquiv e χ,
    by rw [IrrPPrime, Set.mem_setOf_eq, IrrCharIsoClass.mapEquiv_degree]; exact hχ⟩
  invFun := fun ⟨ψ, hψ⟩ => ⟨(IrrCharIsoClass.mapEquiv e).symm ψ,
    by rw [IrrPPrime, Set.mem_setOf_eq, ← IrrCharIsoClass.mapEquiv_degree e
           ((IrrCharIsoClass.mapEquiv e).symm ψ),
           Equiv.apply_symm_apply]; exact hψ⟩
  left_inv := by intro ⟨χ, hχ⟩; simp [Equiv.symm_apply_apply]
  right_inv := by intro ⟨ψ, hψ⟩; simp [Equiv.apply_symm_apply]

/-- Isomorphic groups have the same number of p'-irreducible characters. -/
theorem IrrPPrime.card_eq_of_mulEquiv (e : G ≃* H) (p : ℕ) :
    Nat.card (IrrPPrime G p) = Nat.card (IrrPPrime H p) :=
  Nat.card_congr (IrrPPrime.equivOfMulEquiv e p)

end Transfer

/-! ## McKay conjecture for groups with normal Sylow subgroups

When a Sylow `p`-subgroup `P` is normal in `G`, the normalizer `N_G(P)` equals
the whole group `G`. In this case, the McKay conjecture holds trivially since
both sides count the same set of characters (up to the canonical identification
of `G` with `↥⊤`). -/

section NormalSylow

/-- When the normalizer of a Sylow subgroup is the whole group, the McKay conjecture
holds via the canonical group isomorphism between `G` and `↥⊤`. -/
theorem mckay_of_normalizer_eq_top
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [Group G] [Fintype G]
    (P : Sylow p G) (h : (P : Subgroup G).normalizer = ⊤) :
    Nat.card (IrrPPrime G p) =
      Nat.card (IrrPPrime ((P : Subgroup G).normalizer) p) := by
  conv_rhs => rw [h]
  exact IrrPPrime.card_eq_of_mulEquiv
    (Subgroup.topEquiv (G := G)).symm p

/-- When the Sylow `p`-subgroup is normal, the McKay conjecture holds.
This is because `N_G(P) = G` for a normal subgroup. -/
theorem mckay_of_normal_sylow
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [Group G] [Fintype G]
    (P : Sylow p G) (hP : (P : Subgroup G).Normal) :
    Nat.card (IrrPPrime G p) =
      Nat.card (IrrPPrime ((P : Subgroup G).normalizer) p) :=
  mckay_of_normalizer_eq_top p G P (Subgroup.normalizer_eq_top (P : Subgroup G))

end NormalSylow

/-! ## McKay conjecture for abelian groups

In an abelian (commutative) group, every subgroup is normal. In particular, every
Sylow `p`-subgroup is normal, so `N_G(P) = G` and the McKay conjecture holds. -/

section Abelian

/-- The McKay conjecture holds for all abelian groups and all primes. -/
theorem mckay_comm_group
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [CommGroup G] [Fintype G]
    (P : Sylow p G) :
    Nat.card (IrrPPrime G p) =
      Nat.card (IrrPPrime ((P : Subgroup G).normalizer) p) :=
  mckay_of_normal_sylow p G P inferInstance

end Abelian

/-! ## McKay conjecture for cyclic groups of prime order

Cyclic groups of prime order are abelian, so the McKay conjecture holds by the
abelian case. We formalize the cyclic group of order `p` as
`Multiplicative (ZMod p)`. -/

section CyclicPrime

/-- The McKay conjecture holds for cyclic groups of prime order.
Since `Multiplicative (ZMod p)` is abelian, every Sylow subgroup is normal,
so `N_G(P) = G` and both sides of the McKay equation are equal. -/
theorem mckay_cyclic_prime
    (p : ℕ) [Fact (Nat.Prime p)]
    (q : ℕ) [Fact (Nat.Prime q)]
    (P : Sylow q (Multiplicative (ZMod p))) :
    Nat.card (IrrPPrime (Multiplicative (ZMod p)) q) =
      Nat.card (IrrPPrime ((P : Subgroup (Multiplicative (ZMod p))).normalizer) q) :=
  mckay_comm_group q (Multiplicative (ZMod p)) P

end CyclicPrime

/-! ## McKay conjecture for S₃ (the symmetric group on 3 elements) at p = 3

The symmetric group `S₃ = Equiv.Perm (Fin 3)` has order 6. Its Sylow 3-subgroup
has order 3 and is normal (there is a unique Sylow 3-subgroup, the alternating
group `A₃`). Therefore the McKay conjecture holds for `S₃` at `p = 3`. -/

section S3

/-- The Sylow 3-subgroup of S₃ is normal. Since |S₃| = 6, the number of Sylow
3-subgroups divides 2 and is ≡ 1 mod 3, so there is exactly one. A unique Sylow
subgroup is necessarily normal. -/
instance S3_sylow3_normal (P : Sylow 3 (Equiv.Perm (Fin 3))) :
    (P : Subgroup (Equiv.Perm (Fin 3))).Normal := by
  have h_unique : ∀ Q : Sylow 3 (Equiv.Perm (Fin 3)), Q = P := by
    intro Q
    have h_card : Nat.card (Sylow 3 (Equiv.Perm (Fin 3))) = 1 := by
      have h_mod : Nat.card (Sylow 3 (Equiv.Perm (Fin 3))) ≡ 1 [MOD 3] :=
        (fun P => card_sylow_modEq_one 3 (Equiv.Perm (Fin 3))) P
      have h_dvd : Nat.card (Sylow 3 (Equiv.Perm (Fin 3))) ∣ Nat.card (Equiv.Perm (Fin 3)) := by
        convert Subgroup.card_quotient_dvd_card
          (Subgroup.normalizer (P : Subgroup (Equiv.Perm (Fin 3)))) using 1
        exact Sylow.card_eq_card_quotient_normalizer P
      simp_all +decide [Fintype.card_perm]
      have := Nat.le_of_dvd (by decide) h_dvd
      interval_cases Fintype.card (Sylow 3 (Equiv.Perm (Fin 3))) <;> trivial
    rw [Nat.card_eq_one_iff_unique] at h_card
    exact h_card.1.elim Q P
  refine' ⟨fun g hg => _⟩
  exact fun g₃ => h_unique (MulAut.conj g₃ • P) ▸ Set.mem_smul_set.mpr ⟨_, hg, rfl⟩

/-- The McKay conjecture holds for S₃ at p = 3. The unique Sylow 3-subgroup is
normal, so `N_{S₃}(P) = S₃` and both sides count the same characters. -/
theorem mckay_S3_p3
    (P : Sylow 3 (Equiv.Perm (Fin 3))) :
    Nat.card (IrrPPrime (Equiv.Perm (Fin 3)) 3) =
      Nat.card (IrrPPrime ((P : Subgroup (Equiv.Perm (Fin 3))).normalizer) 3) :=
  mckay_of_normal_sylow 3 (Equiv.Perm (Fin 3)) P inferInstance

end S3

/-! ## McKay conjecture for D₃ (the dihedral group of order 6) at p = 3

The dihedral group `DihedralGroup 3` has order 6. Its Sylow 3-subgroup is normal
(same reasoning as S₃: the number of Sylow 3-subgroups divides 2 and is ≡ 1 mod 3).
Therefore the McKay conjecture holds at `p = 3`. -/

section D3

/-- The Sylow 3-subgroup of D₃ is normal. Since |D₃| = 6, the number of Sylow
3-subgroups divides 2 and is ≡ 1 mod 3, so there is exactly one. -/
instance D3_sylow3_normal (P : Sylow 3 (DihedralGroup 3)) :
    (P : Subgroup (DihedralGroup 3)).Normal := by
  have h_unique : ∀ Q : Sylow 3 (DihedralGroup 3), Q = P := by
    intro Q
    have h_card : Nat.card (Sylow 3 (DihedralGroup 3)) = 1 := by
      have h_mod : Nat.card (Sylow 3 (DihedralGroup 3)) ≡ 1 [MOD 3] :=
        card_sylow_modEq_one 3 (DihedralGroup 3)
      have h_dvd : Nat.card (Sylow 3 (DihedralGroup 3)) ∣ Nat.card (DihedralGroup 3) := by
        convert Subgroup.card_quotient_dvd_card
          (Subgroup.normalizer (P : Subgroup (DihedralGroup 3))) using 1
        exact Sylow.card_eq_card_quotient_normalizer P
      simp_all +decide
      have : Fintype.card (Sylow 3 (DihedralGroup 3)) ≤ 6 :=
        Nat.le_of_dvd (by decide) h_dvd
      interval_cases Fintype.card (Sylow 3 (DihedralGroup 3)) <;> trivial
    rw [Nat.card_eq_one_iff_unique] at h_card
    exact h_card.1.elim Q P
  constructor
  intro n hn g
  have := h_unique (MulAut.conj g • P)
  exact this ▸ Set.mem_smul_set.mpr ⟨n, hn, rfl⟩

/-- The McKay conjecture holds for D₃ at p = 3. The unique Sylow 3-subgroup is
normal, so `N_{D₃}(P) = D₃` and both sides count the same characters. -/
theorem mckay_D3_p3
    (P : Sylow 3 (DihedralGroup 3)) :
    Nat.card (IrrPPrime (DihedralGroup 3) 3) =
      Nat.card (IrrPPrime ((P : Subgroup (DihedralGroup 3)).normalizer) 3) :=
  mckay_of_normal_sylow 3 (DihedralGroup 3) P inferInstance

end D3

end

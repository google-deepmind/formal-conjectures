import Mathlib

open scoped TensorProduct
open scoped BigOperators

-- TODO(Paul): change this to `Set.univ \ Set.range f` ?
abbrev Free {A : Type*} {R : Type*} (f : R → A) :=
  {a : A // a ∉ Set.range f}

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {R : Type*} [Fintype R] [DecidableEq R]

def PurePartOfContraction
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ C)
    (vA : A → V) (vB : B → V) :
    (C → V) :=
  let inc : (Free fst) ⊕ (Free snd) → A ⊕ B := Sum.map (fun i => i) (fun i => i)
  let vSum : A ⊕ B → V := fun s =>
    match s with
    | Sum.inl a => vA a
    | Sum.inr a => vB a
  vSum ∘ inc ∘ f.symm

lemma PurePart_Invariance_Right
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ C)
    (vA : A → V) (vB : B → V)
    (i : Set.range snd)
    (x : V):
    PurePartOfContraction fst snd f vA (Function.update vB i.val x) = PurePartOfContraction fst snd f vA vB := by
  simp only [PurePartOfContraction, ← Function.comp_assoc, f.symm.surjective.right_cancellable]
  funext j
  cases j with
  | inl a => simp
  | inr b => grind

lemma PurePart_Invariance_Left
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ C)
    (vA : A → V) (vB : B → V)
    (i : Set.range fst)
    (x : V):
    PurePartOfContraction fst snd f (Function.update vA i.val x) vB = PurePartOfContraction fst snd f vA vB := by
  simp only [PurePartOfContraction, ← Function.comp_assoc,
    f.symm.surjective.right_cancellable]
  funext j
  cases j with
  | inl a => grind
  | inr b => simp

lemma PurePart_Update_Right
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ C)
    (vA : A → V) (vB : B → V)
    (i : Free snd)
    (x : V):
    PurePartOfContraction fst snd f vA (Function.update vB i.val x) = Function.update (PurePartOfContraction fst snd f vA vB) (f (Sum.inr i)) x := by
  simp [PurePartOfContraction]
  funext t
  by_cases h : t = f (Sum.inr i)
  . grind
  · rw [Function.update_of_ne h]
    cases hft : f.symm t with
    | inl a => simp [hft]
    | inr a => grind

lemma PurePart_Update_Left
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ C)
    (vA : A → V) (vB : B → V)
    (i : Free fst)
    (x : V):
    PurePartOfContraction fst snd f (Function.update vA i.val x) vB = Function.update (PurePartOfContraction fst snd f vA vB) (f (Sum.inl i)) x := by
  simp [PurePartOfContraction]
  funext t
  by_cases h : t = f (Sum.inl i)
  . grind
  · rw [Function.update_of_ne h]
    cases hft : f.symm t with
    | inr a => simp [hft]
    | inl a => grind

noncomputable def ScalarPartOfContraction
    (fst : R → A) (snd : R → B)
    (vA : A → V) (vB : B → V) : ℝ :=
  let scalars : R → ℝ := fun r =>
    inner ℝ (vA (fst r)) (vB (snd r))
  ∏ r : R, scalars r

lemma ScalarPart_Invariance_Right
    (fst : R → A) (snd : R → B)
    (vA : A → V) (vB : B → V)
    (i : Free snd)
    (x : V):
    ScalarPartOfContraction fst snd vA (Function.update vB i.val x) = ScalarPartOfContraction fst snd vA vB := by
  simp [ScalarPartOfContraction]
  grind

lemma ScalarPart_Invariance_Left
    (fst : R → A) (snd : R → B)
    (vA : A → V) (vB : B → V)
    (i : Free fst)
    (x : V):
    ScalarPartOfContraction fst snd (Function.update vA i.val x) vB = ScalarPartOfContraction fst snd vA vB := by
  simp [ScalarPartOfContraction]
  grind

lemma ScalarPart_Update_Add_Right
    (fst : R → A) (snd : R → B)
    (hInjsnd : Function.Injective snd)
    (vA : A → V) (vB : B → V)
    (i : Set.range snd)
    (x y: V):
    ScalarPartOfContraction fst snd vA (Function.update vB i.val (x + y)) = (ScalarPartOfContraction fst snd vA (Function.update vB i.val x)) + (ScalarPartOfContraction fst snd vA (Function.update vB i.val y)) := by
  simp only [ScalarPartOfContraction]
  rcases i.property with ⟨r₀, hr₀i⟩
  have hr₀R : r₀ ∈ (Finset.univ : Finset R) := by simp
  have hsplit (z : V) :=
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset R))
      (f := fun r => inner ℝ (vA (fst r)) (Function.update vB i z (snd r)))
      (a := r₀)
      (h := hr₀R)
      ).symm
  have prod_const (z : V) :
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (
          if snd r = i then
            z
          else vB (snd r)
          ))
      =
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (vB (snd r))) := by
    refine Finset.prod_congr rfl ?_
    grind
  simp_rw [hsplit]
  simp [Function.update, hr₀i, inner_add_right, add_mul, prod_const]

lemma ScalarPart_Update_Add_Left
    (fst : R → A) (snd : R → B)
    (hInjfst : Function.Injective fst)
    (vA : A → V) (vB : B → V)
    (i : Set.range fst)
    (x y: V):
    ScalarPartOfContraction fst snd (Function.update vA i.val (x + y)) vB = (ScalarPartOfContraction fst snd (Function.update vA i.val x) vB) + (ScalarPartOfContraction fst snd (Function.update vA i.val y) vB) := by
  simp only [ScalarPartOfContraction]
  rcases i.property with ⟨r₀, hr₀i⟩
  have hr₀R : r₀ ∈ (Finset.univ : Finset R) := by simp
  have hsplit (z : V) :=
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset R))
      (f := fun r => inner ℝ (Function.update vA i z (fst r)) (vB (snd r)))
      (a := r₀)
      (h := hr₀R)
      ).symm
  have prod_const (z : V) :
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (
          if fst r = i then
            z
          else vA (fst r)
          ) (vB (snd r)))
      =
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (vB (snd r))) := by
    refine Finset.prod_congr rfl ?_
    grind
  simp [hsplit]
  simp [Function.update, hr₀i, inner_add_left, add_mul, prod_const]

lemma ScalarPart_Update_Mul_Right
    (fst : R → A) (snd : R → B)
    (hInjsnd : Function.Injective snd)
    (vA : A → V) (vB : B → V)
    (i : Set.range snd)
    (c : ℝ) (x : V) :
    ScalarPartOfContraction fst snd vA (Function.update vB i.val (c • x)) = c • ScalarPartOfContraction fst snd vA (Function.update vB i.val x) := by
  simp only [ScalarPartOfContraction]
  rcases i.property with ⟨r₀, hr₀i⟩
  have hr₀R : r₀ ∈ (Finset.univ : Finset R) := by simp
  have hsplit (z : V) :=
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset R))
      (f := fun r => inner ℝ (vA (fst r)) (Function.update vB i z (snd r)))
      (a := r₀)
      (h := hr₀R)
      ).symm
  have prod_const (z : V) :
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (
          if snd r = i then
            z
          else vB (snd r)
          ))
      =
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (vB (snd r))) := by
    refine Finset.prod_congr rfl ?_
    grind
  simp [hsplit]
  simp [Function.update, hr₀i, inner_smul_right, mul_assoc, prod_const]

lemma ScalarPart_Update_Mul_Left
    (fst : R → A) (snd : R → B)
    (hInjsnd : Function.Injective fst)
    (vA : A → V) (vB : B → V)
    (i : Set.range fst)
    (c : ℝ) (x : V) :
    ScalarPartOfContraction fst snd (Function.update vA i.val (c • x)) vB = c • ScalarPartOfContraction fst snd (Function.update vA i.val x) vB := by
  simp only [ScalarPartOfContraction]
  rcases i.property with ⟨r₀, hr₀i⟩
  have hr₀R : r₀ ∈ (Finset.univ : Finset R) := by simp
  have hsplit (z : V) :=
    (Finset.mul_prod_erase
      (s := (Finset.univ : Finset R))
      (f := fun r => inner ℝ (Function.update vA i z (fst r)) (vB (snd r)))
      (a := r₀)
      (h := hr₀R)
      ).symm
  have prod_const (z : V) :
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (
          if fst r = i then
            z
          else vA (fst r)
          ) (vB (snd r)))
      =
    (∏ r ∈ ((Finset.univ : Finset R).erase r₀),
        inner ℝ (vA (fst r)) (vB (snd r))) := by
    refine Finset.prod_congr rfl ?_
    grind
  simp [hsplit]
  simp [Function.update, hr₀i, inner_smul_left, mul_assoc, prod_const]

noncomputable def EvaluateContraction
    {m : ℕ}
    (fst : R → A) (snd : R → B)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m)
    (vA : A → V) (vB : B → V) :
    (⨂[ℝ]^m V) :=
  letI pure : Fin m → V := PurePartOfContraction fst snd f vA vB
  letI scal : ℝ := ScalarPartOfContraction fst snd vA vB
  scal • (PiTensorProduct.tprod ℝ pure)

noncomputable def ContractionWithPure
    {l m : ℕ}
    (fst : R → A) (snd : R → (Fin l))
    (hInjsnd : Function.Injective snd)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m)
    (vA : A → V) :
    MultilinearMap ℝ (fun _ : Fin l => V) (⨂[ℝ]^m V) := by
  refine
    { toFun := ?toFun,
      map_update_add' := ?map_update_add',
      map_update_smul' := ?map_update_smul'
      }
  . intro vB
    let hDec : DecidableEq (Fin l) := instDecidableEqFin l
    exact EvaluateContraction fst snd f vA vB
  . intro _ vB i x y
    by_cases hi : i ∈ Set.range snd
    . have hScalar := ScalarPart_Update_Add_Right fst snd (B := Fin l) hInjsnd vA vB ⟨i,hi⟩ x y
      have hPure (z : V) := PurePart_Invariance_Right fst snd f vA vB ⟨i,hi⟩ z
      simp [EvaluateContraction, hScalar, hPure, add_smul]
    . have hPure (z : V) := PurePart_Update_Right fst snd f vA vB ⟨i, hi⟩ z
      have hScalar (z : V) := ScalarPart_Invariance_Right fst snd vA vB ⟨i,hi⟩ z
      simp [EvaluateContraction, hScalar, hPure]
  . intro _ vB i c x
    by_cases hi : i ∈ Set.range snd
    . have hScalar :=
        ScalarPart_Update_Mul_Right fst snd hInjsnd vA vB ⟨i,hi⟩ c x
      have hPure (z : V) := PurePart_Invariance_Right fst snd f vA vB ⟨i,hi⟩ z
      simp [EvaluateContraction, hScalar, hPure, mul_smul]
    . have hScalar (z : V) := ScalarPart_Invariance_Right fst snd vA vB ⟨i, hi⟩ z
      have hPure (z : V) := PurePart_Update_Right fst snd f vA vB ⟨i,hi⟩ z
      simp [EvaluateContraction, hScalar, hPure, ← smul_assoc, mul_comm]

lemma ContractionWithPure_update_add
    {l m : ℕ}
    (fst : R → A) (snd : R → (Fin l))
    (hInjfst : Function.Injective fst)
    (hInjsnd : Function.Injective snd)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m)
    (vA : A → V) (i : A) (x y : V):
      ContractionWithPure fst snd hInjsnd f (Function.update vA i (x + y)) = (ContractionWithPure fst snd hInjsnd f (Function.update vA i x)) + (ContractionWithPure fst snd hInjsnd f (Function.update vA i y)) := by
  simp only [ContractionWithPure]
  ext vB
  by_cases hi : i ∈ Set.range fst
  . have hScalar := ScalarPart_Update_Add_Left fst snd hInjfst vA vB ⟨i,hi⟩ x y
    have hPure (z : V) := PurePart_Invariance_Left fst snd f vA vB ⟨i,hi⟩ z
    simp [EvaluateContraction, hScalar, hPure, add_smul]
  . have hPure (z : V) := PurePart_Update_Left fst snd f vA vB ⟨i, hi⟩ z
    have hScalar (z : V) := ScalarPart_Invariance_Left fst snd vA vB ⟨i,hi⟩ z
    simp [EvaluateContraction, hScalar, hPure]

lemma ContractionWithPure_update_mul
    {l m : ℕ}
    (fst : R → A) (snd : R → (Fin l))
    (hInjfst : Function.Injective fst)
    (hInjsnd : Function.Injective snd)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m)
    (vA : A → V) (i : A) (c : ℝ) (x : V):
      ContractionWithPure fst snd hInjsnd f (Function.update vA i (c • x)) = c • (ContractionWithPure fst snd hInjsnd f (Function.update vA i x)) := by
  simp only [ContractionWithPure]
  ext vB
  by_cases hi : i ∈ Set.range fst
  . have hScalar :=
      ScalarPart_Update_Mul_Left fst snd hInjfst vA vB ⟨i,hi⟩ c x
    have hPure (z : V) := PurePart_Invariance_Left fst snd f vA vB ⟨i,hi⟩ z
    simp [EvaluateContraction, hScalar, hPure, mul_smul]
  . have hScalar (z : V) :=
      ScalarPart_Invariance_Left fst snd vA vB ⟨i, hi⟩ z
    have hPure (z : V) :=
      PurePart_Update_Left fst snd f vA vB ⟨i,hi⟩ z
    simp [EvaluateContraction, hScalar, hPure, ← smul_assoc, mul_comm]

noncomputable def MultiLinearTensorContraction
    {k l m : ℕ}
    (fst : R → (Fin k)) (snd : R → (Fin l))
    (hInjfst : Function.Injective fst)
    (hInjsnd : Function.Injective snd)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m) :
      MultilinearMap ℝ (fun _ : Fin k => V) (⨂[ℝ]^l V →ₗ[ℝ] ⨂[ℝ]^m V) where
  toFun va := PiTensorProduct.lift (ContractionWithPure fst snd hInjsnd f va)
  map_update_add' := by
    intro _ vA i x y
    simpa using congrArg PiTensorProduct.lift
      (ContractionWithPure_update_add
        (fst := fst) (snd := snd)
        (hInjfst := hInjfst) (hInjsnd := hInjsnd)
        (f := f) (vA := vA) (i := i) (x := x) (y := y))
  map_update_smul' := by
    intro _ vA i c x
    simpa using congrArg PiTensorProduct.lift
      (ContractionWithPure_update_mul
        (fst := fst) (snd := snd)
        (hInjfst := hInjfst) (hInjsnd := hInjsnd)
        (f := f) (vA := vA) (i := i) (c := c) (x := x))

noncomputable def TensorContraction
    {k l m : ℕ}
    (fst : R → (Fin k)) (snd : R → (Fin l))
    (hInjfst : Function.Injective fst)
    (hInjsnd : Function.Injective snd)
    (f : (Free fst) ⊕ (Free snd) ≃ Fin m) :
      (⨂[ℝ]^k V) →ₗ[ℝ] ⨂[ℝ]^l V →ₗ[ℝ] ⨂[ℝ]^m V :=
  PiTensorProduct.lift (MultiLinearTensorContraction fst snd hInjfst hInjsnd f)

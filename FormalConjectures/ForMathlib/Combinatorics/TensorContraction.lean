import Mathlib

open scoped TensorProduct
open scoped BigOperators

variable (V : Type*)[NormedAddCommGroup V] [InnerProductSpace ℝ V]

def finIccEquiv (k : ℕ) : Fin k ≃ Set.Icc (1 : ℕ) k :=
  { toFun := fun i =>
    ⟨i.1 + 1,
      by
        have hi : i.1 < k := i.2
        constructor
        · -- 1 ≤ i.1 + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
        · -- i.1 + 1 ≤ k
          exact Nat.succ_le_of_lt hi⟩
  , invFun := fun i =>
    -- send n ∈ [1,k] ↦ n-1 as an element of Fin k
    ⟨i.1 - 1,
      by
        -- we need: i.1 - 1 < k
        have h₁ : 1 ≤ i.1 := i.2.1
        have h₂ : i.1 ≤ k := i.2.2
        -- from 1 ≤ i.1 we get 0 < i.1
        have hpos : 0 < i.1 := Nat.succ_le_iff.mp h₁
        -- i.1 - 1 < i.1
        have hlt₁ : i.1 - 1 < i.1 := Nat.sub_lt (Nat.succ_le_of_lt hpos) (Nat.succ_pos _)
        -- so i.1 - 1 < k by transitivity
        exact lt_of_lt_of_le hlt₁ h₂⟩
  , left_inv := by
      intro i
    -- show: (i ↦ i+1 ↦ (i+1)-1) = i
      cases i with
      | mk n hn =>
      -- the underlying ℕ equality is (n + 1) - 1 = n
      -- then Fin extensionality finishes it
        apply Fin.ext
        simp
    , right_inv := by
      intro i
    -- show: (n ↦ n-1 ↦ (n-1)+1) = n  for n ∈ [1,k]
      cases i with
      | mk n hIcc =>
        have h₁ : 1 ≤ n := hIcc.1
        have hpos : 0 < n := Nat.succ_le_iff.mp h₁
        apply Subtype.ext
        -- as ℕ: (n - 1) + 1 = n
        have : n - 1 + 1 = n := Nat.sub_add_cancel h₁
        simp [this]
  }

/-- Turn `v : Fin k → V` into a function on `{1,…,k}`. -/
def finFunToIccFun {V : Type*} {k : ℕ} (v : Fin k → V) : Set.Icc (1 : ℕ) k → V :=
  fun i => v ((finIccEquiv k).symm i)

lemma finFunToIccFun_update {V : Type*} {k : ℕ} [DecidableEq (Fin k)] (v : Fin k → V) (i : Fin k) (x : V) :
  finFunToIccFun (k := k) (Function.update v i x) = Function.update (finFunToIccFun (k := k) v) (finIccEquiv k i) x := by
    funext j
    let e := finIccEquiv k
    by_cases h : j = e i
    ·
      subst h
      simp [finFunToIccFun, Function.update, e]
    ·
      have hij : e.symm j ≠ i := by
        intro h'
        apply h
        have := e.apply_symm_apply j
        simpa [h'] using this.symm
      simp [finFunToIccFun, Function.update, h, hij, e]

/-- Turn `w : {1,…,k} → V` into a function on `Fin k`. -/
def iccFunToFinFun {V : Type*} {k : ℕ} (w : Set.Icc (1 : ℕ) k → V) : Fin k → V :=
  fun i => w ((finIccEquiv k) i)

lemma iccFunToFinFun_update {V : Type*} {k : ℕ} [DecidableEq (Fin k)] (v : Set.Icc (1 : ℕ) k → V) (i : Set.Icc (1 : ℕ) k) (x : V) :
  iccFunToFinFun (k := k) (Function.update v i x) = Function.update (iccFunToFinFun (k := k) v) ((finIccEquiv k).symm i) x := by
    funext j
    let e := (finIccEquiv k)
    by_cases h : j = e.symm i
    ·
      subst h
      simp [iccFunToFinFun, Function.update, e]
    ·
      have hij : e j ≠ i := by
        intro h'
        apply h
        have := e.symm_apply_apply j
        simpa [h'] using this.symm
      simp [iccFunToFinFun, Function.update, h, hij, e]

def PurePartOfContraction {k l m : ℕ} (R : Set (ℕ × ℕ))
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) :
    (Fin m → V) := by
    let A := (Set.Icc 1 k \ Prod.fst '' R : Set ℕ)
    let B := (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)
    let Ainc : A → Set.Icc 1 k := fun i => by
      have hi : i.val ∈ (Set.Icc 1 k) := by simpa using i.property.left
      exact ⟨i.val,hi⟩
    let Binc : B → Set.Icc 1 l := fun i => by
      have hi : i.val ∈ (Set.Icc 1 l) := by simpa using i.property.left
      exact ⟨i.val,hi⟩
    let inc : A ⊕ B → (Set.Icc 1 k) ⊕ (Set.Icc 1 l) := Sum.map Ainc Binc
    let vSum : (Set.Icc 1 k) ⊕ (Set.Icc 1 l) → V := fun s =>
      match s with
      | Sum.inl a => v a
      | Sum.inr a => (finFunToIccFun m_1) a
    let prefun : A ⊕ B → V := vSum ∘ inc
    exact iccFunToFinFun (prefun ∘ f.symm)

variable {α β γ : Type*}

theorem comp_right_cancel (f : α ≃ β) {g h : β → γ} :
    (g ∘ f = h ∘ f) ↔ g = h := by
  constructor
  · -- → direction: cancel `f` on the right
    intro hcomp
    funext b
    -- apply the equality of functions at `f.symm b`
    have := congrArg (fun (k : α → γ) => k (f.symm b)) hcomp
    -- now `(g ∘ f) (f.symm b) = (h ∘ f) (f.symm b)` simplifies to `g b = h b`
    simpa using this
  · -- ← direction: if `g = h` then trivially `g ∘ f = h ∘ f`
    intro hgh
    subst hgh
    rfl

lemma PurePart_Invariance_Right {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Fin l) (hi : (finIccEquiv l i).val ∈ Prod.snd '' R) (x : V):
    PurePartOfContraction V R f v (Function.update m_1 i x) = PurePartOfContraction V R f v m_1 := by
    simp [PurePartOfContraction]
    apply congrArg (iccFunToFinFun)
    rw [comp_right_cancel]
    have hupdate : finFunToIccFun (k := l) (Function.update m_1 i x) = Function.update (finFunToIccFun (k := l) m_1) (finIccEquiv l i) x :=
      finFunToIccFun_update (v := m_1) (i := i) (x := x)
    rw [hupdate]
    funext j
    cases j with
    | inl a =>
      simp
    | inr b =>
      rcases b with ⟨n, hn⟩
      have hn_not : n ∉ Prod.snd '' R := hn.2
      have hn_Icc : n ∈ Set.Icc (1 : ℕ) l := hn.1
      let y : Set.Icc (1 : ℕ) l := ⟨n, hn_Icc⟩
      have hneq : y ≠ finIccEquiv l i := by
        intro hEq
        have hmem' : y.1 ∈ Prod.snd '' R := by
          have : (finIccEquiv l i).1 ∈ Prod.snd '' R := hi
          simpa [hEq] using this
        have : n ∈ Prod.snd '' R := by simpa [y] using hmem'
        exact hn_not this
      simp [Function.update, y, hneq]

lemma PurePart_Invariance_Left {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Set.Icc 1 k) (hi : i.val ∈ Prod.fst '' R) (x : V):
    PurePartOfContraction V R f (Function.update v i x) m_1 = PurePartOfContraction V R f v m_1 := by
    classical
    simp [PurePartOfContraction]
    apply congrArg (iccFunToFinFun)
    rw [comp_right_cancel]
    funext j
    cases j with
    | inr a =>
      simp
    | inl b =>
      rcases b with ⟨n, hn⟩
      have hn_not : n ∉ Prod.fst '' R := hn.2
      have hn_Icc : n ∈ Set.Icc (1 : ℕ) k := hn.1
      let y : Set.Icc (1 : ℕ) k := ⟨n, hn_Icc⟩
      have hneq : y ≠ i := by
        intro hEq
        have hmem' : y.1 ∈ Prod.fst '' R := by
          have : i.1 ∈ Prod.fst '' R := hi
          simpa [hEq] using this
        have : n ∈ Prod.fst '' R := by simpa [y] using hmem'
        exact hn_not this
      simp [Function.update, y, hneq]

lemma PurePart_Update_Right {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Fin l) (hi : (finIccEquiv l i).val ∈ Set.Icc 1 l \ Prod.snd '' R) (x : V):
    PurePartOfContraction V R f v (Function.update m_1 i x) = Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi⟩))) x := by
  classical
  simp [PurePartOfContraction]
  rw [← iccFunToFinFun_update]
  apply congrArg (iccFunToFinFun)
  funext t
  by_cases h : t = f (Sum.inr ⟨(finIccEquiv l i).val, hi⟩)
  . subst h
    have hIcc :
        (⟨(finIccEquiv l i).val, hi.1⟩ : Set.Icc 1 l)
          = finIccEquiv l i := by
      apply Subtype.ext
      simp  -- same underlying nat; proof is irrelevant
    -- Now simplify both sides.
    simp [Function.update]
    rw [finFunToIccFun_update]
    simp
  · have h_ne : t ≠ f (Sum.inr ⟨(finIccEquiv l i).val, hi⟩) := h
    rw [Function.update_of_ne h_ne, finFunToIccFun_update]
    cases hft : f.symm t with
    | inl a =>
      simp [hft]
    | inr a =>
      simp [hft]
      rw [Function.update_of_ne]
      intro h1
      have h_a : a = ⟨(finIccEquiv l i).val, hi⟩ := by
        ext
        have := congrArg (fun x : Set.Icc 1 l => (x : ℕ)) h1
        simpa using this
      exact h (by
        have := congrArg f hft
        simpa [h_a] using this)

lemma PurePart_Update_Left {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Set.Icc 1 k) (hi : i.val ∈ Set.Icc 1 k \ Prod.fst '' R) (x : V):
    PurePartOfContraction V R f (Function.update v i x) m_1 = Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i,hi⟩))) x := by
  classical
  simp [PurePartOfContraction]
  rw [← iccFunToFinFun_update]
  apply congrArg (iccFunToFinFun)
  funext t
  by_cases h : t = f (Sum.inl ⟨i.val, hi⟩)
  . subst h
    simp [Function.update]
  · have h_ne : t ≠ f (Sum.inl ⟨i.val, hi⟩) := h
    rw [Function.update_of_ne h_ne]
    cases hft : f.symm t with
    | inr a =>
      simp [hft]
    | inl a =>
      simp [hft]
      rw [Function.update_of_ne]
      intro h1
      have h_a : a = ⟨i.val, hi⟩ := by
        ext
        have := congrArg (fun x : Set.Icc 1 k => (x : ℕ)) h1
        simpa using this
      exact h (by
        have := congrArg f hft
        simpa [h_a] using this)

noncomputable def ScalarPartOfContraction {k l : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) :
    ℝ := by
    classical
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite := (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite := hIccFin.subset hR
    let scalars : ℕ × ℕ → ℝ := fun r =>
      if hr : r ∈ R then
        have h1 : r.1 ∈ Set.Icc 1 k := (hR hr).1
        have h2 : r.2 ∈ Set.Icc 1 l := (hR hr).2
        inner ℝ (v ⟨r.1,h1⟩) (finFunToIccFun m_1 ⟨r.2,h2⟩)
      else
        1
    exact ∏ r ∈ hRfin.toFinset, scalars r

lemma ScalarPart_Invariance_Right {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Fin l) (hi : (finIccEquiv l i).val ∈ Set.Icc 1 l \ Prod.snd '' R) (x : V):
    ScalarPartOfContraction V R hR v (Function.update m_1 i x) = ScalarPartOfContraction V R hR v m_1 := by
    classical
    simp [ScalarPartOfContraction]
    apply Finset.prod_congr rfl
    intro r hrFin
    by_cases hr : r∈ R
    .
      simp [hr, finFunToIccFun_update, Function.update]
      have h2 : r.2 ∈ Set.Icc 1 l := (hR hr).2
      have hneq : (⟨r.2, h2⟩ : Set.Icc 1 l) ≠ finIccEquiv l i := by
        intro hEq
        have hr2_in : r.2 ∈ Prod.snd '' R := by
          refine ⟨r, hr, ?_⟩
          rfl
        have hNat : (finIccEquiv l i).val = r.2 := by
          have := congrArg (fun (z : Set.Icc 1 l) => (z : ℕ)) hEq
          simpa using this.symm
        have : (finIccEquiv l i).val ∈ Prod.snd '' R := by
          simpa [hNat] using hr2_in
        exact hi.2 this
      simp [hneq]
    .
      simp [hr]

lemma ScalarPart_Invariance_Left {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Set.Icc 1 k) (hi : i.val ∈ Set.Icc 1 k \ Prod.fst '' R) (x : V):
    ScalarPartOfContraction V R hR (Function.update v i x)  m_1 = ScalarPartOfContraction V R hR v m_1 := by
    classical
    simp [ScalarPartOfContraction]
    apply Finset.prod_congr rfl
    intro r hrFin
    by_cases hr : r∈ R
    .
      simp [hr, Function.update]
      have h2 : r.1 ∈ Set.Icc 1 k := (hR hr).1
      have hneq : (⟨r.1, h2⟩ : Set.Icc 1 k) ≠ i := by
        intro hEq
        have hr1_in : r.1 ∈ Prod.fst '' R := by
          refine ⟨r, hr, ?_⟩
          rfl
        have hNat : i.val = r.1 := by
          have := congrArg (fun (z : Set.Icc 1 k) => (z : ℕ)) hEq
          simpa using this.symm
        have : i.val ∈ Prod.fst '' R := by
          simpa [hNat] using hr1_in
        exact hi.2 this
      simp [hneq]
    .
      simp [hr]

lemma ScalarPart_Update_Add_Right {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjsnd : Set.InjOn Prod.snd R)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Fin l) (hi : (finIccEquiv l i).val ∈ Prod.snd '' R) (x y: V):
    ScalarPartOfContraction V R hR v (Function.update m_1 i (x + y)) = (ScalarPartOfContraction V R hR v (Function.update m_1 i x)) + (ScalarPartOfContraction V R hR v (Function.update m_1 i y)) := by
    classical
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite := (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite := hIccFin.subset hR
    simp [ScalarPartOfContraction, finFunToIccFun_update]
    rcases hi with ⟨r₀, hr₀R, hr₀snd⟩
    have hr₀S : r₀ ∈ hRfin.toFinset :=
      by simpa using hRfin.mem_toFinset.mpr hr₀R
    have hsplit_xy :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ (v ⟨r.1, ((hR h).1)⟩) (Function.update (finFunToIccFun m_1) (finIccEquiv l i) (x + y) ⟨r.2, ((hR h).2)⟩)
          else 1)
      hr₀S).symm
    have hsplit_x :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ (v ⟨r.1, ((hR h).1)⟩) (Function.update (finFunToIccFun m_1) (finIccEquiv l i) x ⟨r.2, ((hR h).2)⟩)
          else 1)
      hr₀S).symm
    have hsplit_y :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ (v ⟨r.1, ((hR h).1)⟩) (Function.update (finFunToIccFun m_1) (finIccEquiv l i) y ⟨r.2, ((hR h).2)⟩)
          else 1)
      hr₀S).symm
    simp [hsplit_xy, hsplit_x, hsplit_y, hr₀R]
    simp [Function.update, hr₀snd, inner_add_right, add_mul]
        -- Define the “tail product” as a function of a vector `z`.
    -- Note: we avoid `?_` by getting the Icc-memberships from `hR` *inside* the proof.
    have prod_const :
        ∀ z : V,
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩)
                (if (⟨r.2, hIl⟩ : Set.Icc 1 l) = (finIccEquiv l i) then z
                 else finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1)
          =
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1) := by
        intro z
        refine Finset.prod_congr rfl ?_
        intro r hr
        classical
        by_cases hrR : r ∈ R
        ·
          have hr_ne : r ≠ r₀ := (Finset.mem_erase.mp hr).1
          have hIk : r.1 ∈ Set.Icc 1 k := (hR hrR).1
          have hIl : r.2 ∈ Set.Icc 1 l := (hR hrR).2
          have hvals_ne : r.2 ≠ r₀.2 := by
            intro h_eq
            have : r = r₀ :=
              hInjsnd hrR hr₀R (by simpa [Prod.snd] using h_eq)
            exact hr_ne this
          have hcond_false : (⟨r.2, hIl⟩ : Set.Icc 1 l) ≠ (finIccEquiv l i) := by
            intro h_eq
            have hnat : r.2 = finIccEquiv l i :=
              congrArg (fun (t : Set.Icc 1 l) => (t : ℕ)) h_eq
            -- `hr₀snd : r₀.2 = ↑((finIccEquiv l) i)`
            have : r.2 = r₀.2 := by
              simpa [hr₀snd] using hnat
            exact hvals_ne this
          simp [hrR]
          have : ¬ ((⟨r.2, hIl⟩ : Set.Icc 1 l) = (finIccEquiv l) i) := by
            exact hcond_false
          simp [this]
        · -- Case: r ∉ R: both sides are `1`.
          simp [hrR]
    -- Instantiate that lemma at z = x + y, z = x, and z = y.
    have prod_xy := prod_const (x + y)
    have prod_x  := prod_const x
    have prod_y  := prod_const y
    -- All three “tail products” in the goal now collapse to the same base product.
    -- The big equality becomes trivially true.
    simp [prod_xy, prod_x, prod_y]

lemma ScalarPart_Update_Add_Left {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Set.Icc 1 k) (hi : i.val ∈ Prod.fst '' R) (x y: V):
    ScalarPartOfContraction V R hR (Function.update v i (x + y)) m_1 = (ScalarPartOfContraction V R hR (Function.update v i x) m_1) + (ScalarPartOfContraction V R hR (Function.update v i y) m_1) := by
    classical
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite := (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite := hIccFin.subset hR
    simp [ScalarPartOfContraction]
    rcases hi with ⟨r₀, hr₀R, hr₀fst⟩
    have hr₀S : r₀ ∈ hRfin.toFinset :=
      by simpa using hRfin.mem_toFinset.mpr hr₀R
    have hsplit_xy :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ ((Function.update v i (x + y)) ⟨r.1, (hR h).1⟩) ((finFunToIccFun m_1) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    have hsplit_x :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ ((Function.update v i x) ⟨r.1, (hR h).1⟩) ((finFunToIccFun m_1) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    have hsplit_y :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ ((Function.update v i y) ⟨r.1, (hR h).1⟩) ((finFunToIccFun m_1) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    simp [hsplit_xy, hsplit_x, hsplit_y, hr₀R]
    simp [Function.update, hr₀fst, inner_add_left, add_mul]
        -- Define the “tail product” as a function of a vector `z`.
    -- Note: we avoid `?_` by getting the Icc-memberships from `hR` *inside* the proof.
    have prod_const :
        ∀ z : V,
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (if (⟨r.1, hIk⟩ : Set.Icc 1 k) = i then z
                 else v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1)
          =
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1) := by
        intro z
        refine Finset.prod_congr rfl ?_
        intro r hr
        classical
        by_cases hrR : r ∈ R
        ·
          have hr_ne : r ≠ r₀ := (Finset.mem_erase.mp hr).1
          have hIk : r.1 ∈ Set.Icc 1 k := (hR hrR).1
          have hIl : r.2 ∈ Set.Icc 1 l := (hR hrR).2
          have hvals_ne : r.1 ≠ r₀.1 := by
            intro h_eq
            have : r = r₀ :=
              hInjfst hrR hr₀R (by simpa [Prod.fst] using h_eq)
            exact hr_ne this
          have hcond_false : (⟨r.1, hIk⟩ : Set.Icc 1 k) ≠ i := by
            intro h_eq
            have hnat : r.1 = i :=
              congrArg (fun (t : Set.Icc 1 k) => (t : ℕ)) h_eq
            -- `hr₀snd : r₀.2 = ↑((finIccEquiv l) i)`
            have : r.1 = r₀.1 := by
              simpa [hr₀fst] using hnat
            exact hvals_ne this
          simp [hrR]
          have : ¬ ((⟨r.1, hIk⟩ : Set.Icc 1 k) = i) := by
            exact hcond_false
          simp [this]
        · -- Case: r ∉ R: both sides are `1`.
          simp [hrR]
    -- Instantiate that lemma at z = x + y, z = x, and z = y.
    have prod_xy := prod_const (x + y)
    have prod_x  := prod_const x
    have prod_y  := prod_const y
    -- All three “tail products” in the goal now collapse to the same base product.
    -- The big equality becomes trivially true.
    simp [prod_xy, prod_x, prod_y]

lemma ScalarPart_Update_Mul_Right {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjsnd : Set.InjOn Prod.snd R)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Fin l) (hi : (finIccEquiv l i).val ∈ Prod.snd '' R) (c : ℝ) (x : V) :
    ScalarPartOfContraction V R hR v (Function.update m_1 i (c • x)) = c • ScalarPartOfContraction V R hR v (Function.update m_1 i x) := by
    classical
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite := (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite := hIccFin.subset hR
    simp [ScalarPartOfContraction, finFunToIccFun_update]
    rcases hi with ⟨r₀, hr₀R, hr₀snd⟩
    have hr₀S : r₀ ∈ hRfin.toFinset :=
      by simpa using hRfin.mem_toFinset.mpr hr₀R
    have hsplit_cx :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ (v ⟨r.1, (hR h).1⟩) (Function.update (finFunToIccFun m_1) (finIccEquiv l i) (c • x) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    have hsplit_x :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ (v ⟨r.1, (hR h).1⟩) (Function.update (finFunToIccFun m_1) (finIccEquiv l i) x ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    simp [hsplit_cx, hsplit_x, hr₀R]
    simp [Function.update, hr₀snd]
    simp [inner_smul_right, mul_assoc]
    have prod_const :
        ∀ z : V,
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩)
                (if (⟨r.2, hIl⟩ : Set.Icc 1 l) = (finIccEquiv l i) then z
                 else finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1)
          =
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1) := by
        intro z
        refine Finset.prod_congr rfl ?_
        intro r hr
        classical
        by_cases hrR : r ∈ R
        ·
          have hr_ne : r ≠ r₀ := (Finset.mem_erase.mp hr).1
          have hIk : r.1 ∈ Set.Icc 1 k := (hR hrR).1
          have hIl : r.2 ∈ Set.Icc 1 l := (hR hrR).2
          have hvals_ne : r.2 ≠ r₀.2 := by
            intro h_eq
            have : r = r₀ :=
              hInjsnd hrR hr₀R (by simpa [Prod.snd] using h_eq)
            exact hr_ne this
          have hcond_false : (⟨r.2, hIl⟩ : Set.Icc 1 l) ≠ (finIccEquiv l i) := by
            intro h_eq
            have hnat : r.2 = finIccEquiv l i :=
              congrArg (fun (t : Set.Icc 1 l) => (t : ℕ)) h_eq
            -- `hr₀snd : r₀.2 = ↑((finIccEquiv l) i)`
            have : r.2 = r₀.2 := by
              simpa [hr₀snd] using hnat
            exact hvals_ne this
          simp [hrR]
          have : ¬ ((⟨r.2, hIl⟩ : Set.Icc 1 l) = (finIccEquiv l) i) := by
            exact hcond_false
          simp [this]
        · -- Case: r ∉ R: both sides are `1`.
          simp [hrR]
    have prod_cx := prod_const (c • x)
    have prod_x  := prod_const x
    simp [prod_cx, prod_x]

lemma ScalarPart_Update_Mul_Left {k l m : ℕ} [DecidableEq (Fin k)] [DecidableEq (Fin l)] [DecidableEq (Fin m)] (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) (i : Set.Icc 1 k) (hi : i.val ∈ Prod.fst '' R) (c : ℝ) (x : V) :
    ScalarPartOfContraction V R hR (Function.update v i (c • x)) m_1= c • ScalarPartOfContraction V R hR (Function.update v i x) m_1 := by
    classical
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite := (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite := hIccFin.subset hR
    simp [ScalarPartOfContraction]
    rcases hi with ⟨r₀, hr₀R, hr₀fst⟩
    have hr₀S : r₀ ∈ hRfin.toFinset :=
      by simpa using hRfin.mem_toFinset.mpr hr₀R
    have hsplit_cx :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ ((Function.update v i (c • x)) ⟨r.1, (hR h).1⟩) ((finFunToIccFun m_1) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    have hsplit_x :=
      (Finset.mul_prod_erase
        (s := hRfin.toFinset)
        (a := r₀)
        (f := fun r =>
          if h : r ∈ R then
            inner ℝ ((Function.update v i x) ⟨r.1, (hR h).1⟩) ((finFunToIccFun m_1) ⟨r.2, (hR h).2⟩)
          else 1)
      hr₀S).symm
    simp [hsplit_cx, hsplit_x, hr₀R]
    simp [Function.update, hr₀fst]
    simp [inner_smul_left, mul_assoc]
    have prod_const :
        ∀ z : V,
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (if (⟨r.1, hIk⟩ : Set.Icc 1 k) = i then z
                 else v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1)
          =
          ∏ r ∈ hRfin.toFinset.erase r₀,
            (if hr : r ∈ R then
              let hIk : r.1 ∈ Set.Icc 1 k := (hR hr).1
              let hIl : r.2 ∈ Set.Icc 1 l := (hR hr).2
              inner ℝ (v ⟨r.1, hIk⟩) (finFunToIccFun m_1 ⟨r.2, hIl⟩)
            else 1) := by
        intro z
        refine Finset.prod_congr rfl ?_
        intro r hr
        classical
        by_cases hrR : r ∈ R
        ·
          have hr_ne : r ≠ r₀ := (Finset.mem_erase.mp hr).1
          have hIk : r.1 ∈ Set.Icc 1 k := (hR hrR).1
          have hIl : r.2 ∈ Set.Icc 1 l := (hR hrR).2
          have hvals_ne : r.1 ≠ r₀.1 := by
            intro h_eq
            have : r = r₀ :=
              hInjfst hrR hr₀R (by simpa [Prod.fst] using h_eq)
            exact hr_ne this
          have hcond_false : (⟨r.1, hIk⟩ : Set.Icc 1 k) ≠ i := by
            intro h_eq
            have hnat : r.1 = i :=
              congrArg (fun (t : Set.Icc 1 k) => (t : ℕ)) h_eq
            -- `hr₀snd : r₀.2 = ↑((finIccEquiv l) i)`
            have : r.1 = r₀.1 := by
              simpa [hr₀fst] using hnat
            exact hvals_ne this
          simp [hrR]
          have : ¬ ((⟨r.1, hIk⟩ : Set.Icc 1 k) = i) := by
            exact hcond_false
          simp [this]
        · -- Case: r ∉ R: both sides are `1`.
          simp [hrR]
    have prod_cx := prod_const (c • x)
    have prod_x  := prod_const x
    simp [prod_cx, prod_x]

noncomputable def EvaluateContraction {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (m_1 : Fin l -> V) :
    (⨂[ℝ]^m V) := by
    let pure : Fin m → V := PurePartOfContraction V R f v m_1
    let scal : ℝ := ScalarPartOfContraction V R hR v m_1
    exact scal • (PiTensorProduct.tprod ℝ pure)

noncomputable def ContractionWithPure {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjsnd : Set.InjOn Prod.snd R)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) :
    MultilinearMap ℝ (fun _ : Fin l => V) (⨂[ℝ]^m V) := by
    have hIccFin : (Set.Icc 1 k ×ˢ Set.Icc 1 l).Finite :=
      (Set.finite_Icc 1 k).prod (Set.finite_Icc 1 l)
    have hRfin : R.Finite :=
      hIccFin.subset hR
    let A := (Set.Icc 1 k \ Prod.fst '' R : Set ℕ)
    let B := (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)
    let Ainc : A → Set.Icc 1 k := fun i => by
      have hi : i.val ∈ (Set.Icc 1 k) := by simpa using i.property.left
      exact ⟨i.val,hi⟩
    let Binc : B → Set.Icc 1 l := fun i => by
      have hi : i.val ∈ (Set.Icc 1 l) := by simpa using i.property.left
      exact ⟨i.val,hi⟩
    let inc : A ⊕ B → (Set.Icc 1 k) ⊕ (Set.Icc 1 l) := Sum.map Ainc Binc
    classical
    refine
      { toFun := ?toFun,
        map_update_add' := ?map_update_add',
        map_update_smul' := ?map_update_smul'
        }
    . intro m_1
      exact EvaluateContraction V R hR f v m_1
    . intro _ m_1 i x y
      simp [EvaluateContraction]
      by_cases hi : (finIccEquiv l i).val ∈ Prod.snd '' R
      .
        have hScalar : ScalarPartOfContraction V R hR v (Function.update m_1 i (x + y)) =
          ScalarPartOfContraction V R hR v (Function.update m_1 i x) +
          ScalarPartOfContraction V R hR v (Function.update m_1 i y) := ScalarPart_Update_Add_Right (k := k) (l := l) (m := m) (V := V) (R := R) hR hInjsnd v m_1 i hi x y
        have hPurexy : PurePartOfContraction V R f v (Function.update m_1 i (x + y)) =
          PurePartOfContraction V R f v m_1 := PurePart_Invariance_Right (k := k) (l := l) (m := m) V R f v m_1 i hi (x + y)
        have hPurex : PurePartOfContraction V R f v (Function.update m_1 i x) =
          PurePartOfContraction V R f v m_1 := PurePart_Invariance_Right (k := k) (l := l) (m := m) V R f v m_1 i hi x
        have hPurey : PurePartOfContraction V R f v (Function.update m_1 i y) =
          PurePartOfContraction V R f v m_1 := PurePart_Invariance_Right (k := k) (l := l) (m := m) V R f v m_1 i hi y
        simp [hScalar, hPurexy, hPurex, hPurey, add_smul]
      .
        have hi' : (finIccEquiv l i).val ∈ Set.Icc 1 l \ Prod.snd '' R := by simp [hi]
        have hPurexy : PurePartOfContraction V R f v (Function.update m_1 i (x + y)) =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi'⟩))) (x + y) :=
          PurePart_Update_Right (k := k) (l := l) (m := m) V R f v m_1 i hi' (x + y)
        have hPurex : PurePartOfContraction V R f v (Function.update m_1 i x) =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi'⟩))) x :=
          PurePart_Update_Right (k := k) (l := l) (m := m) V R f v m_1 i hi' x
        have hPurey : PurePartOfContraction V R f v (Function.update m_1 i y) =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi'⟩))) y :=
          PurePart_Update_Right (k := k) (l := l) (m := m) V R f v m_1 i hi' y
        have hScalarxy : ScalarPartOfContraction V R hR v (Function.update m_1 i (x + y)) =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Right (k := k) (l := l) (m := m) V R hR v m_1 i hi' (x + y)
        have hScalarx : ScalarPartOfContraction V R hR v (Function.update m_1 i x) =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Right (k := k) (l := l) (m := m) V R hR v m_1 i hi' x
        have hScalary : ScalarPartOfContraction V R hR v (Function.update m_1 i y) =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Right (k := k) (l := l) (m := m) V R hR v m_1 i hi' y
        simp [hPurexy, hPurex, hPurey, hScalarxy, hScalarx, hScalary]
    . intro _ m_1 i c x
      simp [EvaluateContraction]
      by_cases hi : (finIccEquiv l i).val ∈ Prod.snd '' R
      .
        have hScalar : ScalarPartOfContraction V R hR v (Function.update m_1 i (c • x)) =
          c • ScalarPartOfContraction V R hR v (Function.update m_1 i x) :=
          ScalarPart_Update_Mul_Right (k := k) (l := l) (m := m) (V := V) (R := R) hR hInjsnd v m_1 i hi c x
        have hPurecx : PurePartOfContraction V R f v (Function.update m_1 i (c • x)) =
          PurePartOfContraction V R f v m_1 := PurePart_Invariance_Right (k := k) (l := l) (m := m) V R f v m_1 i hi (c • x)
        have hPurex : PurePartOfContraction V R f v (Function.update m_1 i x) =
          PurePartOfContraction V R f v m_1 := PurePart_Invariance_Right (k := k) (l := l) (m := m) V R f v m_1 i hi x
        simp [hScalar, hPurecx, hPurex, mul_smul]
      .
        have hi' : (finIccEquiv l i).val ∈ Set.Icc 1 l \ Prod.snd '' R := by simp [hi]
        have hScalarcx : ScalarPartOfContraction V R hR v (Function.update m_1 i (c • x)) =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Right (k := k) (l := l) (m := m) (V := V) (R := R) hR v m_1 i hi' (c • x)
        have hScalarx : ScalarPartOfContraction V R hR v (Function.update m_1 i x) =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Right (k := k) (l := l) (m := m) (V := V) (R := R) hR v m_1 i hi' x
        have hPurecx : PurePartOfContraction V R f v (Function.update m_1 i (c • x)) =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi'⟩))) (c • x) :=
          PurePart_Update_Right (k := k) (l := l) (m := m) V R f v m_1 i hi' (c • x)
        have hPurex : PurePartOfContraction V R f v (Function.update m_1 i x) =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inr ⟨(finIccEquiv l i).val, hi'⟩))) x :=
          PurePart_Update_Right (k := k) (l := l) (m := m) V R f v m_1 i hi' x
        simp [hScalarcx, hScalarx, hPurecx, hPurex, ← smul_assoc, mul_comm]

lemma ContractionWithPure_update_add {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (hInjsnd : Set.InjOn Prod.snd R)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (i : Set.Icc 1 k) (x y : V):
      ContractionWithPure V R hR hInjsnd f (Function.update v i (x + y)) = (ContractionWithPure V R hR hInjsnd f (Function.update v i x)) + (ContractionWithPure V R hR hInjsnd f (Function.update v i y)) := by
    classical
    simp [ContractionWithPure]
    ext m_1
    simp [EvaluateContraction]
    by_cases hi : i.val ∈ Prod.fst '' R
    .
      have hScalar : ScalarPartOfContraction V R hR (Function.update v i (x + y)) m_1 =
        ScalarPartOfContraction V R hR (Function.update v i x) m_1 +
        ScalarPartOfContraction V R hR (Function.update v i y) m_1 := ScalarPart_Update_Add_Left (k := k) (l := l) (m := m) (V := V) (R := R) hR hInjfst v m_1 i hi x y
      have hPurexy : PurePartOfContraction V R f (Function.update v i (x + y)) m_1 =
        PurePartOfContraction V R f v m_1 := PurePart_Invariance_Left (k := k) (l := l) (m := m) V R f v m_1 i hi (x + y)
      have hPurex : PurePartOfContraction V R f (Function.update v i x) m_1 =
        PurePartOfContraction V R f v m_1 := PurePart_Invariance_Left (k := k) (l := l) (m := m) V R f v m_1 i hi x
      have hPurey : PurePartOfContraction V R f (Function.update v i y) m_1 =
        PurePartOfContraction V R f v m_1 := PurePart_Invariance_Left (k := k) (l := l) (m := m) V R f v m_1 i hi y
      simp [hScalar, hPurexy, hPurex, hPurey, add_smul]
    .
      have hi' : i.val ∈ Set.Icc 1 k \ Prod.fst '' R := by simp [hi]
      have hPurexy : PurePartOfContraction V R f (Function.update v i (x + y)) m_1 =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i.val, hi'⟩))) (x + y) :=
          PurePart_Update_Left (k := k) (l := l) (m := m) V R f v m_1 i hi' (x + y)
      have hPurex : PurePartOfContraction V R f (Function.update v i x) m_1 =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i.val, hi'⟩))) x :=
          PurePart_Update_Left (k := k) (l := l) (m := m) V R f v m_1 i hi' x
      have hPurey : PurePartOfContraction V R f (Function.update v i y) m_1 =
          Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i.val, hi'⟩))) y :=
          PurePart_Update_Left (k := k) (l := l) (m := m) V R f v m_1 i hi' y
      have hScalarxy : ScalarPartOfContraction V R hR (Function.update v i (x + y)) m_1 =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Left (k := k) (l := l) (m := m) V R hR v m_1 i hi' (x + y)
      have hScalarx : ScalarPartOfContraction V R hR (Function.update v i x) m_1 =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Left (k := k) (l := l) (m := m) V R hR v m_1 i hi' x
      have hScalary : ScalarPartOfContraction V R hR (Function.update v i y) m_1 =
          ScalarPartOfContraction V R hR v m_1 :=
          ScalarPart_Invariance_Left (k := k) (l := l) (m := m) V R hR v m_1 i hi' y
      simp [hPurexy, hPurex, hPurey, hScalarxy, hScalarx, hScalary]

lemma ContractionWithPure_update_mul {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (hInjsnd : Set.InjOn Prod.snd R)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m))
    (v : Set.Icc 1 k → V) (i : Set.Icc 1 k) (c : ℝ) (x : V):
      ContractionWithPure V R hR hInjsnd f (Function.update v i (c • x)) = c • (ContractionWithPure V R hR hInjsnd f (Function.update v i x)) := by
    classical
    simp [ContractionWithPure]
    ext m_1
    simp [EvaluateContraction]
    by_cases hi : i.val ∈ Prod.fst '' R
    .
      have hScalar : ScalarPartOfContraction V R hR (Function.update v i (c • x)) m_1 =
        c • ScalarPartOfContraction V R hR (Function.update v i x) m_1 :=
        ScalarPart_Update_Mul_Left (k := k) (l := l) (m := m) (V := V) (R := R) hR hInjfst v m_1 i hi c x
      have hPurecx : PurePartOfContraction V R f (Function.update v i (c • x)) m_1 =
        PurePartOfContraction V R f v m_1 := PurePart_Invariance_Left (k := k) (l := l) (m := m) V R f v m_1 i hi (c • x)
      have hPurex : PurePartOfContraction V R f (Function.update v i x) m_1 =
        PurePartOfContraction V R f v m_1 := PurePart_Invariance_Left (k := k) (l := l) (m := m) V R f v m_1 i hi x
      simp [hScalar, hPurecx, hPurex, mul_smul]
    .
      have hi' : i.val ∈ Set.Icc 1 k \ Prod.fst '' R := by simp [hi]
      have hScalarcx : ScalarPartOfContraction V R hR (Function.update v i (c • x)) m_1 =
        ScalarPartOfContraction V R hR v m_1 :=
        ScalarPart_Invariance_Left (k := k) (l := l) (m := m) (V := V) (R := R) hR v m_1 i hi' (c • x)
      have hScalarx : ScalarPartOfContraction V R hR (Function.update v i x) m_1=
        ScalarPartOfContraction V R hR v m_1 :=
        ScalarPart_Invariance_Left (k := k) (l := l) (m := m) (V := V) (R := R) hR v m_1 i hi' x
      have hPurecx : PurePartOfContraction V R f (Function.update v i (c • x)) m_1 =
        Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i.val, hi'⟩))) (c • x) :=
        PurePart_Update_Left (k := k) (l := l) (m := m) V R f v m_1 i hi' (c • x)
      have hPurex : PurePartOfContraction V R f (Function.update v i x) m_1 =
        Function.update (PurePartOfContraction V R f v m_1) ((finIccEquiv m).symm (f (Sum.inl ⟨i.val, hi'⟩))) x :=
        PurePart_Update_Left (k := k) (l := l) (m := m) V R f v m_1 i hi' x
      simp [hScalarcx, hScalarx, hPurecx, hPurex, ← smul_assoc, mul_comm]

noncomputable def MultiLinearTensorContraction {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (hInjsnd : Set.InjOn Prod.snd R)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m)) :
      MultilinearMap ℝ (fun _ : Fin k => V) (⨂[ℝ]^l V →ₗ[ℝ] ⨂[ℝ]^m V) := by
    classical
    refine
      { toFun := ?toFun,
        map_update_add' := ?map_update_add',
        map_update_smul' := ?map_update_smul'
        }
    . intro v
      let w : (Set.Icc 1 k) → V := finFunToIccFun v
      exact PiTensorProduct.lift (ContractionWithPure V R hR hInjsnd f w)
    . intro _ m_1 i x y
      let wxy := finFunToIccFun (k := k) (Function.update m_1 i (x + y))
      let wx := finFunToIccFun (Function.update m_1 i x)
      let wy := finFunToIccFun (Function.update m_1 i y)
      have hwxy : wxy = Function.update (finFunToIccFun m_1) (finIccEquiv k i) (x + y) := by
        exact finFunToIccFun_update (v := m_1) (i := i) (x := x + y)
      have hwx : wx = Function.update (finFunToIccFun m_1) (finIccEquiv k i) x := by
        exact finFunToIccFun_update (v := m_1) (i := i) (x := x)
      have hwy : wy = Function.update (finFunToIccFun m_1) (finIccEquiv k i) y := by
        exact finFunToIccFun_update (v := m_1) (i := i) (x := y)
      simp [wxy, wx, wy, hwxy, hwx, hwy]
      rw [ContractionWithPure_update_add V R hR hInjfst hInjsnd f (v := finFunToIccFun m_1) (i := finIccEquiv k i) (x := x) (y := y)]
      simp [PiTensorProduct.lift.map_add]
    . intro _ m_1 i c x
      let wcx := finFunToIccFun (Function.update m_1 i (c • x))
      let wx := finFunToIccFun (Function.update m_1 i x)
      have hwcx : wcx = Function.update (finFunToIccFun m_1) (finIccEquiv k i) (c • x) := by
        exact finFunToIccFun_update (v := m_1) (i := i) (x := c • x)
      have hwx : wx = Function.update (finFunToIccFun m_1) (finIccEquiv k i) x := by
        exact finFunToIccFun_update (v := m_1) (i := i) (x := x)
      simp [wcx, wx, hwcx, hwx]
      rw [ContractionWithPure_update_mul V R hR hInjfst hInjsnd f (v := finFunToIccFun m_1) (i := finIccEquiv k i) (c := c) (x := x)]
      simp [PiTensorProduct.lift.map_smul]

noncomputable def TensorContraction {k l m : ℕ} (R : Set (ℕ × ℕ))
    (hR : R ⊆ Set.Icc 1 k ×ˢ Set.Icc 1 l)
    (hInjfst : Set.InjOn Prod.fst R)
    (hInjsnd : Set.InjOn Prod.snd R)
    /- `f` is a bijection from the disjoint union `([k] \ π₁(R)) ⊔ ([l] \ π₁(R))` to `[m]`. -/
    (f : ((Set.Icc 1 k \ Prod.fst '' R : Set ℕ) ⊕ (Set.Icc 1 l \ Prod.snd '' R : Set ℕ)) ≃ (Set.Icc 1 m)) :
      (⨂[ℝ]^k V) →ₗ[ℝ] ⨂[ℝ]^l V →ₗ[ℝ] ⨂[ℝ]^m V :=
  PiTensorProduct.lift (MultiLinearTensorContraction V R hR hInjfst hInjsnd f)

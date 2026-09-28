129.lean/-
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
# Erdős Problem 129

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)

As observed by Antonio Girao, the problem as written is false: already $R(n; 3, 2)$ grows
exponentially in $n$. We prove the explicit lower bound $2 ^ {\lfloor n / 100 \rfloor} < R(n; 3, 2)$
for $n \ge 100$ (`Erdos129.two_pow_lt_R`) by a first moment argument. It uses $\gg n^2$
edge-disjoint triangles inside every set of $n$ vertices.
-/

@[expose] public section

open Finset

namespace Erdos129

/-- Under the edge colouring `c` of $K_N$, every edge inside the vertex set `T` has colour `i`,
i.e. `T` spans a monochromatic clique of colour `i`. -/
def IsMonoClique {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) (T : Finset (Fin N)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c s(x, y) = i

/-- `N` has the Ramsey property for `(n, k, r)`: for every `r`-colouring of the edges of $K_N$
there is a set `S` of `n` vertices and a colour `i` such that `S` contains no $K_k$ all of whose
edges have colour `i`. -/
def HasRamseyProperty (n k r N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin r, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ i : Fin r, ∀ T ⊆ S, T.card = k → ¬ IsMonoClique c i T

/-- $R(n; k, r)$: the smallest `N` with the Ramsey property for `(n, k, r)`. -/
noncomputable def R (n k r : ℕ) : ℕ := sInf {N | HasRamseyProperty n k r N}

/-! ### Counting colourings -/

/-- Fixing the colour on a set `T` of coordinates divides the count by `|α| ^ |T|`, provided the
other condition `Q` only depends on coordinates outside `T`. -/
@[category API, AMS 5]
theorem card_filter_and_const_on {E α : Type*} [Fintype E] [DecidableEq E] [Fintype α]
    [DecidableEq α] (T : Finset E) (a : α) (Q : (E → α) → Prop) [DecidablePred Q]
    (hQ : ∀ χ χ' : E → α, (∀ e ∉ T, χ e = χ' e) → (Q χ ↔ Q χ')) :
    (univ.filter (fun χ => Q χ ∧ ∀ e ∈ T, χ e = a)).card * Fintype.card α ^ T.card =
      (univ.filter Q).card := by
  let eqv : {χ : E → α // Q χ ∧ ∀ e ∈ T, χ e = a} × (T → α) ≃ {χ : E → α // Q χ} :=
    { toFun := fun p => ⟨fun e => if h : e ∈ T then p.2 ⟨e, h⟩ else p.1.1 e,
        (hQ _ _ (fun e he => by simp [he])).mpr p.1.2.1⟩
      invFun := fun χ => (⟨fun e => if e ∈ T then a else χ.1 e,
        (hQ _ _ (fun e he => by simp [he])).mpr χ.2, fun e he => by simp [he]⟩,
        fun e => χ.1 e.1)
      left_inv := by
        rintro ⟨⟨χ, hχ1, hχ2⟩, f⟩
        refine Prod.ext (Subtype.ext (funext fun e => ?_)) (funext fun e => ?_)
        · by_cases he : e ∈ T <;> simp [he, hχ2]
        · simp
      right_inv := by
        rintro ⟨χ, hχ⟩
        refine Subtype.ext (funext fun e => ?_)
        by_cases he : e ∈ T <;> simp [he] }
  have := Fintype.card_congr eqv
  rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_subtype, Fintype.card_fun,
    Fintype.card_coe] at this
  exact this

/-- Probability that none of a family of pairwise disjoint sets of at most three edges is
monochromatic in a fixed colour `a` is at most `(7/8) ^ (number of sets)`. -/
@[category API, AMS 5]
theorem card_filter_forall_not_const {E ι : Type*} [Fintype E] [DecidableEq E] [DecidableEq ι]
    (a : Fin 2) (T : ι → Finset E) (J : Finset ι) (hT : ∀ j ∈ J, (T j).card ≤ 3)
    (hdisj : (J : Set ι).PairwiseDisjoint T) :
    (univ.filter (fun χ : E → Fin 2 => ∀ j ∈ J, ¬ ∀ e ∈ T j, χ e = a)).card * 8 ^ J.card ≤
      7 ^ J.card * 2 ^ Fintype.card E := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    have ih' := ih (fun j' hj' => hT j' (mem_insert_of_mem hj'))
      (hdisj.subset (by simp))
    set P := fun χ : E → Fin 2 => ∀ j ∈ J, ¬ ∀ e ∈ T j, χ e = a with hP
    have key := card_filter_and_const_on (T j) a P (by
      intro χ χ' h
      simp only [P]
      refine forall₂_congr fun j' hj' => not_congr (forall₂_congr fun e he => ?_)
      have hne : j ≠ j' := fun h => hj (h ▸ hj')
      have hd : Disjoint (T j) (T j') :=
        hdisj (mem_insert_self j J) (mem_insert_of_mem hj') hne
      rw [h e (disjoint_right.mp hd he)])
    have hsplit : (univ.filter (fun χ : E → Fin 2 => ∀ j' ∈ insert j J,
        ¬ ∀ e ∈ T j', χ e = a)).card +
        (univ.filter (fun χ => P χ ∧ ∀ e ∈ T j, χ e = a)).card = (univ.filter P).card := by
      rw [← card_union_of_disjoint]
      · congr 1
        ext χ
        simp only [mem_union, mem_filter, mem_univ, true_and, forall_mem_insert, P]
        tauto
      · rw [disjoint_left]
        intro χ h1 h2
        simp only [mem_filter, mem_univ, true_and, forall_mem_insert] at h1 h2
        exact h1.1 h2.2
    rw [Fintype.card_fin] at key
    set X := (univ.filter (fun χ : E → Fin 2 => ∀ j' ∈ insert j J,
        ¬ ∀ e ∈ T j', χ e = a)).card
    set Y := (univ.filter (fun χ => P χ ∧ ∀ e ∈ T j, χ e = a)).card
    set Z := (univ.filter P).card
    set p := 2 ^ (T j).card with hp
    have hp8 : p ≤ 8 := by
      have := hT j (mem_insert_self j J)
      calc p ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
        _ = 8 := by norm_num
    have hp0 : 0 < p := by positivity
    have h8 : 8 * X ≤ 7 * Z := by
      have h1 : X * p + Z = Z * p := by rw [← hsplit, add_mul, key, hsplit]
      nlinarith
    rw [card_insert_of_notMem hj, pow_succ, pow_succ]
    calc X * (8 ^ J.card * 8) = 8 * X * 8 ^ J.card := by ring
      _ ≤ 7 * Z * 8 ^ J.card := Nat.mul_le_mul_right _ h8
      _ = 7 * (Z * 8 ^ J.card) := by ring
      _ ≤ 7 * (7 ^ J.card * 2 ^ Fintype.card E) := Nat.mul_le_mul_left _ ih'
      _ = 7 ^ J.card * 7 * 2 ^ Fintype.card E := by ring

/-! ### Edge-disjoint triangles in every `n`-set -/

open Classical in
/-- For a fixed `n`-set `S` and colour `i`, the number of colourings in which `S` contains no
triangle of colour `i` is at most `(7/8) ^ ((n/3)^2)` times the total. -/
@[category API, AMS 5]
theorem card_no_mono_triangle_le (N n : ℕ) (S : Finset (Fin N)) (hS : S.card = n) (i : Fin 2) :
    (univ.filter (fun c : Sym2 (Fin N) → Fin 2 =>
        ∀ T ⊆ S, T.card = 3 → ¬ IsMonoClique c i T)).card * 8 ^ ((n / 3) ^ 2) ≤
      7 ^ ((n / 3) ^ 2) * 2 ^ Fintype.card (Sym2 (Fin N)) := by
  set t := n / 3
  obtain ⟨g⟩ : Nonempty (Fin 3 × Fin t ↪ S) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hS]
    omega
  set G : Fin 3 × Fin t → Fin N := fun x => (g x).1
  have hG : Function.Injective G := fun x y h => g.injective (Subtype.ext h)
  have hGS : ∀ x, G x ∈ S := fun x => (g x).2
  let Tri : Fin t × Fin t → Finset (Sym2 (Fin N)) := fun p =>
    {s(G (0, p.1), G (1, p.2)), s(G (1, p.2), G (2, p.1 + p.2)), s(G (0, p.1), G (2, p.1 + p.2))}
  have hcard : ∀ p ∈ (univ : Finset (Fin t × Fin t)), (Tri p).card ≤ 3 :=
    fun p _ => card_le_three
  have hdisj : ((univ : Finset (Fin t × Fin t)) : Set (Fin t × Fin t)).PairwiseDisjoint Tri := by
    rintro ⟨a, b⟩ - ⟨a', b'⟩ - hpq
    haveI : NeZero t := ⟨fun h => by have := a.2; omega⟩
    rw [Function.onFun, disjoint_left]
    intro e he1 he2
    simp only [Tri, mem_insert, mem_singleton] at he1 he2
    apply hpq
    rcases he1 with rfl | rfl | rfl <;> rcases he2 with h | h | h <;>
      simp only [Sym2.eq_iff, hG.eq_iff, Prod.mk.injEq, Fin.reduceEq, false_and, and_false,
        or_false, true_and] at h
    all_goals
      obtain ⟨h1, h2⟩ := h
      first
      | (subst h1; subst h2; rfl)
      | (subst h1; rw [add_left_cancel h2])
      | (subst h1; rw [add_right_cancel h2])
  have hsub : (univ.filter (fun c : Sym2 (Fin N) → Fin 2 =>
        ∀ T ⊆ S, T.card = 3 → ¬ IsMonoClique c i T)) ⊆
      univ.filter (fun c : Sym2 (Fin N) → Fin 2 =>
        ∀ p ∈ (univ : Finset (Fin t × Fin t)), ¬ ∀ e ∈ Tri p, c e = i) := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    rintro ⟨a, b⟩ - hall
    simp only [Tri, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hall
    obtain ⟨h1, h2, h3⟩ := hall
    have n01 : G (0, a) ≠ G (1, b) := by rw [Ne, hG.eq_iff]; simp
    have n02 : G (0, a) ≠ G (2, a + b) := by rw [Ne, hG.eq_iff]; simp
    have n12 : G (1, b) ≠ G (2, a + b) := by rw [Ne, hG.eq_iff]; simp
    refine hc {G (0, a), G (1, b), G (2, a + b)} ?_ ?_ ?_
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact hGS _
    · exact card_eq_three.mpr ⟨_, _, _, n01, n02, n12, rfl⟩
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hxy
        | assumption
        | (rw [Sym2.eq_swap]; assumption)
  calc _ ≤ (univ.filter (fun c : Sym2 (Fin N) → Fin 2 =>
        ∀ p ∈ (univ : Finset (Fin t × Fin t)), ¬ ∀ e ∈ Tri p, c e = i)).card * 8 ^ (t ^ 2) :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ 7 ^ (t ^ 2) * 2 ^ Fintype.card (Sym2 (Fin N)) := by
      have := card_filter_forall_not_const i Tri univ hcard hdisj
      simpa [card_univ, Fintype.card_prod, Fintype.card_fin, sq] using this

/-! ### The numerical estimate -/

/-- The numerical estimate behind the first moment argument. -/
@[category API, AMS 5]
theorem choose_mul_lt (n N : ℕ) (hn : 100 ≤ n) (hN : N ≤ 2 ^ (n / 100)) :
    N.choose n * 2 * 7 ^ ((n / 3) ^ 2) < 8 ^ ((n / 3) ^ 2) := by
  set t := n / 3
  obtain ⟨m, hm_def⟩ : ∃ m, m = n / 100 * n + 1 := ⟨_, rfl⟩
  have hm : 6 * m ≤ t ^ 2 := by
    have h1 : n / 100 * 100 ≤ n := Nat.div_mul_le_self n 100
    have h2 : n ≤ 3 * t + 2 := by omega
    have h3 : n / 100 * n * 100 ≤ n * n := by nlinarith
    have h4 : n * n ≤ (3 * t + 2) * (3 * t + 2) := Nat.mul_le_mul h2 h2
    have h5 : 3 * t ≤ n := by omega
    have h6 : 100 * n ≤ n * n := Nat.mul_le_mul_right n hn
    nlinarith
  have hch : N.choose n * 2 ≤ 2 ^ m :=
    calc N.choose n * 2 ≤ N ^ n * 2 := Nat.mul_le_mul_right _ (Nat.choose_le_pow N n)
      _ ≤ (2 ^ (n / 100)) ^ n * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN n)
      _ = 2 ^ m := by rw [hm_def, ← pow_mul, pow_succ]
  obtain ⟨d, hd⟩ : ∃ d, t ^ 2 = 6 * m + d := ⟨t ^ 2 - 6 * m, by omega⟩
  have hm1 : m ≠ 0 := by omega
  calc N.choose n * 2 * 7 ^ (t ^ 2) ≤ 2 ^ m * 7 ^ (t ^ 2) := Nat.mul_le_mul_right _ hch
    _ = (2 * 7 ^ 6) ^ m * 7 ^ d := by rw [hd, pow_add, mul_pow, pow_mul]; ring
    _ < (8 ^ 6) ^ m * 7 ^ d :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by norm_num) hm1) (by positivity)
    _ ≤ (8 ^ 6) ^ m * 8 ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) d)
    _ = 8 ^ (t ^ 2) := by rw [hd, pow_add, pow_mul]

/-! ### Small `N` fail the Ramsey property -/

open Classical in
/-- If $100 \le n$ and $N \le 2 ^ {\lfloor n / 100 \rfloor}$, then `N` does not have the Ramsey
property for `(n, 3, 2)`. -/
@[category API, AMS 5]
theorem not_hasRamseyProperty (n N : ℕ) (hn : 100 ≤ n) (hN : N ≤ 2 ^ (n / 100)) :
    ¬ HasRamseyProperty n 3 2 N := by
  intro h
  set t := n / 3
  set E := Fintype.card (Sym2 (Fin N))
  let bad : Finset (Fin N) → Fin 2 → Finset (Sym2 (Fin N) → Fin 2) := fun S i =>
    univ.filter (fun c => ∀ T ⊆ S, T.card = 3 → ¬ IsMonoClique c i T)
  have hsub : (univ : Finset (Sym2 (Fin N) → Fin 2)) ⊆
      (powersetCard n univ).biUnion (fun S => univ.biUnion (bad S)) := by
    intro c _
    obtain ⟨S, hS, i, hi⟩ := h c
    simp only [mem_biUnion, mem_powersetCard, subset_univ, true_and, mem_univ]
    exact ⟨S, hS, i, by simpa [bad] using hi⟩
  have hbound : ∀ S ∈ powersetCard n (univ : Finset (Fin N)),
      (univ.biUnion (bad S)).card * 8 ^ (t ^ 2) ≤ 2 * (7 ^ (t ^ 2) * 2 ^ E) := by
    intro S hS
    rw [mem_powersetCard] at hS
    calc (univ.biUnion (bad S)).card * 8 ^ (t ^ 2)
        ≤ (∑ i : Fin 2, (bad S i).card) * 8 ^ (t ^ 2) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ i : Fin 2, (bad S i).card * 8 ^ (t ^ 2) := by rw [sum_mul]
      _ ≤ ∑ _i : Fin 2, 7 ^ (t ^ 2) * 2 ^ E :=
          sum_le_sum fun i _ => card_no_mono_triangle_le N n S hS.2 i
      _ = 2 * (7 ^ (t ^ 2) * 2 ^ E) := by simp
  have htot : 2 ^ E * 8 ^ (t ^ 2) ≤ N.choose n * (2 * (7 ^ (t ^ 2) * 2 ^ E)) := by
    calc 2 ^ E * 8 ^ (t ^ 2) = (univ : Finset (Sym2 (Fin N) → Fin 2)).card * 8 ^ (t ^ 2) := by
          simp [card_univ, E]
      _ ≤ ((powersetCard n univ).biUnion (fun S => univ.biUnion (bad S))).card * 8 ^ (t ^ 2) :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ (∑ S ∈ powersetCard n (univ : Finset (Fin N)), (univ.biUnion (bad S)).card) *
            8 ^ (t ^ 2) := Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
            (univ.biUnion (bad S)).card * 8 ^ (t ^ 2) := by rw [sum_mul]
      _ ≤ ∑ _S ∈ powersetCard n (univ : Finset (Fin N)), 2 * (7 ^ (t ^ 2) * 2 ^ E) :=
          sum_le_sum hbound
      _ = N.choose n * (2 * (7 ^ (t ^ 2) * 2 ^ E)) := by
          simp [card_powersetCard, card_univ, Fintype.card_fin]
  have hlt := choose_mul_lt n N hn hN
  have hE : 0 < 2 ^ E := by positivity
  have : N.choose n * (2 * (7 ^ (t ^ 2) * 2 ^ E)) < 2 ^ E * 8 ^ (t ^ 2) := by
    calc N.choose n * (2 * (7 ^ (t ^ 2) * 2 ^ E)) = (N.choose n * 2 * 7 ^ (t ^ 2)) * 2 ^ E := by
          ring
      _ < 8 ^ (t ^ 2) * 2 ^ E := Nat.mul_lt_mul_of_pos_right hlt hE
      _ = 2 ^ E * 8 ^ (t ^ 2) := by ring
  omega

/-! ### Finiteness of `R(n; 3, 2)` via Ramsey's theorem -/

/-- Two-colour Ramsey theorem with the bound $2 ^ {s + t}$. -/
@[category API, AMS 5]
theorem ramsey_two {α : Type*} [DecidableEq α] (c : Sym2 α → Fin 2) :
    ∀ m s t : ℕ, s + t = m → ∀ V : Finset α, 2 ^ m ≤ V.card →
      (∃ A ⊆ V, A.card = s ∧ ∀ x ∈ A, ∀ y ∈ A, x ≠ y → c s(x, y) = 0) ∨
      (∃ A ⊆ V, A.card = t ∧ ∀ x ∈ A, ∀ y ∈ A, x ≠ y → c s(x, y) = 1) := by
  intro m
  induction m with
  | zero =>
    intro s t hst V _
    left
    exact ⟨∅, empty_subset _, by simp; omega, by simp⟩
  | succ m ih =>
    intro s t hst V hV
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · left; exact ⟨∅, empty_subset _, by simp, by simp⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; exact ⟨∅, empty_subset _, by simp, by simp⟩
    have hVne : V.Nonempty := by
      rw [← card_pos]; have := Nat.one_le_two_pow (n := m + 1); omega
    obtain ⟨v, hv⟩ := hVne
    set V0 := (V.erase v).filter (fun x => c s(v, x) = 0)
    set V1 := (V.erase v).filter (fun x => ¬ c s(v, x) = 0)
    have hsum : V0.card + V1.card = V.card - 1 := by
      rw [card_filter_add_card_filter_not, card_erase_of_mem hv]
    have hV1 : ∀ x ∈ V1, c s(v, x) = 1 := by
      intro x hx
      simp only [V1, mem_filter] at hx
      have := hx.2
      omega
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    by_cases h0 : 2 ^ m ≤ V0.card
    · rcases ih (s - 1) t (by omega) V0 h0 with ⟨A, hA, hAc, hAm⟩ | ⟨B, hB, hBc, hBm⟩
      · left
        have hvA : v ∉ A := fun h => by
          have := hA h; simp [V0] at this
        refine ⟨insert v A, ?_, ?_, ?_⟩
        · intro x hx
          rcases mem_insert.mp hx with rfl | hx
          · exact hv
          · exact mem_of_mem_erase (mem_of_mem_filter _ (hA hx))
        · rw [card_insert_of_notMem hvA]; omega
        · intro x hx y hy hxy
          rcases mem_insert.mp hx with hxv | hxA <;> rcases mem_insert.mp hy with hyv | hyA
          · exact absurd (hxv.trans hyv.symm) hxy
          · rw [hxv]; exact (mem_filter.mp (hA hyA)).2
          · rw [hyv, Sym2.eq_swap]; exact (mem_filter.mp (hA hxA)).2
          · exact hAm x hxA y hyA hxy
      · right
        exact ⟨B, hB.trans ((filter_subset _ _).trans (erase_subset _ _)), hBc, hBm⟩
    · have h1 : 2 ^ m ≤ V1.card := by omega
      rcases ih s (t - 1) (by omega) V1 h1 with ⟨A, hA, hAc, hAm⟩ | ⟨B, hB, hBc, hBm⟩
      · left
        exact ⟨A, hA.trans ((filter_subset _ _).trans (erase_subset _ _)), hAc, hAm⟩
      · right
        have hvB : v ∉ B := fun h => by
          have := hB h; simp [V1] at this
        refine ⟨insert v B, ?_, ?_, ?_⟩
        · intro x hx
          rcases mem_insert.mp hx with rfl | hx
          · exact hv
          · exact mem_of_mem_erase (mem_of_mem_filter _ (hB hx))
        · rw [card_insert_of_notMem hvB]; omega
        · intro x hx y hy hxy
          rcases mem_insert.mp hx with hxv | hxB <;> rcases mem_insert.mp hy with hyv | hyB
          · exact absurd (hxv.trans hyv.symm) hxy
          · rw [hxv]; exact hV1 y (hB hyB)
          · rw [hyv, Sym2.eq_swap]; exact hV1 x (hB hxB)
          · exact hBm x hxB y hyB hxy

/-- $4 ^ n$ has the Ramsey property for `(n, 3, 2)`, so $R(n; 3, 2)$ is finite. -/
@[category API, AMS 5]
theorem hasRamseyProperty_four_pow (n : ℕ) : HasRamseyProperty n 3 2 (4 ^ n) := by
  intro c
  have hV : 2 ^ (n + n) ≤ (univ : Finset (Fin (4 ^ n))).card := by
    rw [card_univ, Fintype.card_fin, pow_add, ← mul_pow]; norm_num
  have key : ∀ (A : Finset (Fin (4 ^ n))) (j i : Fin 2), j ≠ i →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → c s(x, y) = j) →
      ∀ T ⊆ A, T.card = 3 → ¬ IsMonoClique c i T := by
    intro A j i hji hA T hT hT3 hmono
    obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp hT3
    have h1 := hmono x (by simp) y (by simp) hxy
    have h2 := hA x (hT (by simp)) y (hT (by simp)) hxy
    exact hji (h2.symm.trans h1)
  rcases ramsey_two c (n + n) n n rfl univ hV with ⟨A, -, hAc, hAm⟩ | ⟨A, -, hAc, hAm⟩
  · exact ⟨A, hAc, 1, key A 0 1 (by decide) hAm⟩
  · exact ⟨A, hAc, 0, key A 1 0 (by decide) hAm⟩

/-! ### Main results -/

/-- Exponential lower bound (Girao): $2 ^ {\lfloor n / 100 \rfloor} < R(n; 3, 2)$ for all
$n \ge 100$. -/
@[category research solved, AMS 5]
theorem two_pow_lt_R (n : ℕ) (hn : 100 ≤ n) : 2 ^ (n / 100) < R n 3 2 := by
  have hne : {N | HasRamseyProperty n 3 2 N}.Nonempty := ⟨_, hasRamseyProperty_four_pow n⟩
  have hmem : HasRamseyProperty n 3 2 (R n 3 2) := Nat.sInf_mem hne
  by_contra hle
  push_neg at hle
  exact not_hasRamseyProperty n _ hn hle hmem

/-- Even the "for all sufficiently large $n$" version of the bound fails for two colours:
for no $C \ge 0$ does $R(n; 3, 2) < C ^ {\sqrt{n}}$ hold eventually. -/
@[category research solved, AMS 5]
theorem not_eventually_R_lt (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, (R n 3 2 : ℝ) < C ^ Real.sqrt n := by
  intro h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  set k := max (max k₀ M) 1
  set n := 10000 * k ^ 2
  have hk1 : 1 ≤ k := le_max_right _ _
  have hkM : M ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hkk : k₀ ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hkn : k ≤ n := by show k ≤ 10000 * k ^ 2; nlinarith
  have hnM : M ≤ n := le_trans hkM hkn
  have hn100 : 100 ≤ n := by show 100 ≤ 10000 * k ^ 2; nlinarith
  have hsqrt : Real.sqrt (n : ℝ) = ((100 * k : ℕ) : ℝ) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    push_cast [n]; ring
  have hlt := hM n hnM
  rw [hsqrt, Real.rpow_natCast] at hlt
  have hCk : C ≤ 2 ^ k := le_trans hk₀.le (pow_le_pow_right₀ (by norm_num) hkk)
  have hdiv : n / 100 = 100 * k * k := by
    simp only [n]; rw [show 10000 * k ^ 2 = 100 * k * k * 100 by ring]; simp
  have hlow := two_pow_lt_R n hn100
  rw [hdiv] at hlow
  have : C ^ (100 * k) ≤ ((2 ^ (100 * k * k) : ℕ) : ℝ) := by
    calc C ^ (100 * k) ≤ ((2 : ℝ) ^ k) ^ (100 * k) := pow_le_pow_left₀ hC hCk _
      _ = ((2 ^ (100 * k * k) : ℕ) : ℝ) := by push_cast; rw [← pow_mul]; ring_nf
  have hlow' : ((2 ^ (100 * k * k) : ℕ) : ℝ) < (R n 3 2 : ℝ) := by exact_mod_cast hlow
  linarith

/--
Let $R(n;k,r)$ be the smallest $N$ such that if the edges of $K_N$ are $r$-coloured then there is
a set of $n$ vertices which does not contain a copy of $K_k$ in at least one of the $r$ colours.
Prove that there is a constant $C=C(r)>1$ such that $R(n;3,r) < C^{\sqrt{n}}$.

As written, this is false (Girao): see `two_pow_lt_R`.
-/
@[category research solved, AMS 5]
theorem erdos_129 : answer(False) ↔
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  change False ↔ _
  refine ⟨False.elim, fun h => ?_⟩
  obtain ⟨C, hC, hall⟩ := h 2 le_rfl
  exact not_eventually_R_lt C (by linarith) (Filter.Eventually.of_forall hall)

end Erdos129

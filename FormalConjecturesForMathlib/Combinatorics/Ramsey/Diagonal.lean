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


public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Lattice
public import FormalConjecturesForMathlib.Combinatorics.Ramsey

@[expose] public section

/-!
# Erdős–Szekeres 1935 upper bound for the diagonal Ramsey number

**Statement (Erdős–Szekeres 1935):** For every `k : ℕ`, the diagonal Ramsey number satisfies
`R(k, k) ≤ 4 ^ k`.

**Proof sketch.** Use the symmetric recursion `R(s, t) ≤ R(s-1, t) + R(s, t-1)` with base
cases `R(0, t) = R(s, 0) = 1`. Induction on `s + t` then gives `R(s, t) ≤ C(s+t, s)`; for
`s = t = k` this is `R(k, k) ≤ C(2k, k) ≤ 4 ^ k` (the Catalan-like central binomial
coefficient bound).

**Reference:** [ES35] Erdős, P. and Szekeres, G. (1935). "A combinatorial problem in
geometry." *Compositio Math.* **2**, pp. 463–470.
-/

namespace Combinatorics
namespace Diagonal

/-- A **2-edge-colouring of K_n** — symmetric function `Fin n → Fin n → Fin 2`. -/
structure EdgeColouring (n : ℕ) where
  /-- Underlying 2-colouring. -/
  toFun : Fin n → Fin n → Fin 2
  /-- Symmetry: colour is independent of edge orientation. -/
  symm : ∀ i j, toFun i j = toFun j i

instance (n : ℕ) : CoeFun (EdgeColouring n) (fun _ => Fin n → Fin n → Fin 2) := ⟨EdgeColouring.toFun⟩

/-- `S : Finset (Fin n)` is **monochromatic of colour c** under `χ` if every pair of
distinct vertices in `S` receives colour `c`. -/
def IsMonochromaticClique {n : ℕ} (χ : EdgeColouring n)
    (S : Finset (Fin n)) (c : Fin 2) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → χ u v = c

/-- `IsRamsey n k` asserts that every 2-edge-colouring of `K_n` contains a monochromatic
`K_k` (of either colour). -/
def IsRamsey (n k : ℕ) : Prop :=
  ∀ χ : EdgeColouring n, ∃ (S : Finset (Fin n)) (c : Fin 2),
    S.card = k ∧ IsMonochromaticClique χ S c

/-- The **diagonal Ramsey number** `R(k, k)` — the least `n` such that every 2-edge-
colouring of `K_n` contains a monochromatic `K_k`. -/
noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  sInf { n | IsRamsey n k }

/-- The empty subset is a monochromatic `K_0` under any colouring. -/
lemma isRamsey_zero : IsRamsey 0 0 := by
  intro _χ
  refine ⟨∅, 0, by simp, ?_⟩
  intro u hu _ _ _; exact (Finset.notMem_empty _ hu).elim

/-- Every 1-vertex graph has a monochromatic `K_1` (the vertex itself). -/
lemma isRamsey_one : IsRamsey 1 1 := by
  intro _χ
  refine ⟨{0}, 0, by simp, ?_⟩
  intro u hu v hv huv
  simp only [Finset.mem_singleton] at hu hv
  exact absurd (hu.trans hv.symm) huv

/-- **Base case.** `R(0, 0) = 0`: the empty clique trivially exists in the empty graph,
so the infimum of `{n | IsRamsey n 0}` is `0`. -/
lemma ramseyNumber_zero : ramseyNumber 0 = 0 := by
  have h : (0 : ℕ) ∈ {n | IsRamsey n 0} := isRamsey_zero
  exact Nat.le_zero.mp (Nat.sInf_le h)

/-- **Base case.** `R(1, 1) ≤ 1`: any 1-vertex graph witnesses the monochromatic `K_1`. -/
lemma ramseyNumber_one_le : ramseyNumber 1 ≤ 1 :=
  Nat.sInf_le isRamsey_one

/-- **Central binomial bound (Mathlib wrapper).** `C(2n, n) ≤ 4 ^ n`.

This specialises `Nat.choose_middle_le_pow : (2n+1).choose n ≤ 4^n` by observing that
`(2n).choose n ≤ (2n+1).choose n` via the monotonicity lemma `Nat.choose_le_succ`. -/
lemma central_binomial_le_four_pow (n : ℕ) : (2 * n).choose n ≤ 4 ^ n := by
  have h₁ : (2 * n).choose n ≤ (2 * n + 1).choose n := Nat.choose_le_succ (2 * n) n
  exact h₁.trans (Nat.choose_middle_le_pow n)

/-- **Erdős–Szekeres binomial bound at `s = t = k`.**
`C(2k - 2, k - 1) ≤ 4 ^ (k - 1)` for `k ≥ 1`.

This is the specialisation of the general `R(s, t) ≤ C(s + t - 2, s - 1)` bound to
`s = t = k`, packaged as a numeric inequality on binomial coefficients. -/
lemma choose_two_mul_sub_two_sub_one_le_four_pow {k : ℕ} (hk : 1 ≤ k) :
    (2 * k - 2).choose (k - 1) ≤ 4 ^ (k - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
  -- `k = m + 1`, so `2k - 2 = 2m` and `k - 1 = m`.
  have h₁ : 2 * (m + 1) - 2 = 2 * m := by lia
  have h₂ : m + 1 - 1 = m := by lia
  rw [h₁, h₂]
  exact central_binomial_le_four_pow m

/-- `4 ^ (k - 1) ≤ 4 ^ k` for any `k`. -/
lemma four_pow_sub_one_le_four_pow (k : ℕ) : 4 ^ (k - 1) ≤ 4 ^ k :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

/-! ## Off-diagonal Ramsey via a subset-indexed predicate

Rather than introduce an auxiliary `EdgeColouring` restricted to a subtype, we phrase the
off-diagonal Ramsey statement as a property of an arbitrary `Finset (Fin n)` of sufficient
cardinality inside a colouring of `K_n`. This lets the recursion "restrict to the red
(resp. blue) neighbours of a vertex" without rebuilding the colouring. -/

/-- `HasRamseyProperty N s t` asserts: for every `n`, every 2-edge-colouring `χ` of `K_n`,
and every `V : Finset (Fin n)` with `V.card ≥ N`, the subset `V` contains either a
monochromatic-of-colour-`0` subset of size `s` or a monochromatic-of-colour-`1` subset of
size `t`.

This is the "off-diagonal Ramsey number does not exceed `N`" form of the classical
Erdős–Szekeres Ramsey recurrence. -/
def HasRamseyProperty (N s t : ℕ) : Prop :=
  ∀ {n : ℕ} (χ : EdgeColouring n) (V : Finset (Fin n)), N ≤ V.card →
    (∃ S ⊆ V, S.card = s ∧ IsMonochromaticClique χ S 0) ∨
    (∃ S ⊆ V, S.card = t ∧ IsMonochromaticClique χ S 1)

/-- **Monotonicity.** If `N ≤ N'` then `HasRamseyProperty N s t → HasRamseyProperty N' s t`. -/
lemma HasRamseyProperty.mono {N N' s t : ℕ} (hNN' : N ≤ N') (h : HasRamseyProperty N s t) :
    HasRamseyProperty N' s t := by
  intro n χ V hV
  exact h χ V (hNN'.trans hV)

/-- **Base case `s = 0`.** Any `V` contains an empty red `K_0`. -/
lemma hasRamseyProperty_zero_left (N t : ℕ) : HasRamseyProperty N 0 t := by
  intro n χ V _hV
  refine Or.inl ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro u hu _ _ _
  exact (Finset.notMem_empty _ hu).elim

/-- **Base case `t = 0`.** Any `V` contains an empty blue `K_0`. -/
lemma hasRamseyProperty_zero_right (N s : ℕ) : HasRamseyProperty N s 0 := by
  intro n χ V _hV
  refine Or.inr ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro u hu _ _ _
  exact (Finset.notMem_empty _ hu).elim

/-- **Base case `s = 1`.** Any nonempty `V` contains a singleton red `K_1`. -/
lemma hasRamseyProperty_one_left (t : ℕ) : HasRamseyProperty 1 1 t := by
  intro n χ V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inl ⟨{v}, by simpa using hv, by simp, ?_⟩
  intro u hu w hw huw
  simp only [Finset.mem_singleton] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-- **Base case `t = 1`.** Any nonempty `V` contains a singleton blue `K_1`. -/
lemma hasRamseyProperty_one_right (s : ℕ) : HasRamseyProperty 1 s 1 := by
  intro n χ V hV
  obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Or.inr ⟨{v}, by simpa using hv, by simp, ?_⟩
  intro u hu w hw huw
  simp only [Finset.mem_singleton] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-- A monochromatic clique is preserved under passing to a subset. -/
lemma IsMonochromaticClique.subset {n : ℕ} {χ : EdgeColouring n}
    {S T : Finset (Fin n)} {c : Fin 2} (hST : S ⊆ T)
    (h : IsMonochromaticClique χ T c) : IsMonochromaticClique χ S c :=
  fun u hu v hv huv => h u (hST hu) v (hST hv) huv

/-- Inserting a vertex `v` into a monochromatic clique of colour `c` yields a larger
monochromatic clique, provided every vertex of the clique is connected to `v` by an edge
of colour `c` and `v` is not already in the clique. -/
lemma IsMonochromaticClique.insert {n : ℕ} {χ : EdgeColouring n}
    {S : Finset (Fin n)} {c : Fin 2} (h : IsMonochromaticClique χ S c)
    (v₀ : Fin n) (_hv₀ : v₀ ∉ S) (hvS : ∀ u ∈ S, χ v₀ u = c) :
    IsMonochromaticClique χ (insert v₀ S) c := by
  intro u hu w hw huw
  rcases Finset.mem_insert.mp hu with hu_eq | hu'
  · rcases Finset.mem_insert.mp hw with hw_eq | hw'
    · exact (huw (hu_eq.trans hw_eq.symm)).elim
    · rw [hu_eq]; exact hvS w hw'
  · rcases Finset.mem_insert.mp hw with hw_eq | hw'
    · rw [hw_eq, χ.symm u v₀]; exact hvS u hu'
    · exact h u hu' w hw' huw

/-- **Pigeonhole step: splitting `V \ {v}` by colour.** For any vertex `v ∈ V`, the set
`V.erase v` partitions into red-neighbours of `v` and blue-neighbours of `v`, and the
cardinalities sum to `V.card - 1`. -/
lemma card_red_blue_split {n : ℕ} (χ : EdgeColouring n) (V : Finset (Fin n))
    {v : Fin n} (hv : v ∈ V) :
    ((V.erase v).filter (fun u => χ v u = 0)).card
      + ((V.erase v).filter (fun u => χ v u = 1)).card = V.card - 1 := by
  classical
  have hsplit :
      ((V.erase v).filter (fun u => χ v u = 0)).card
        + ((V.erase v).filter (fun u => ¬ χ v u = 0)).card = (V.erase v).card :=
    Finset.card_filter_add_card_filter_not (s := V.erase v) (fun u => χ v u = 0)
  have hne_one : ∀ u, ¬ (χ v u = 0) ↔ χ v u = 1 := by
    intro u; omega
  have hrw : ((V.erase v).filter (fun u => ¬ χ v u = 0)).card
      = ((V.erase v).filter (fun u => χ v u = 1)).card := by
    congr 1
    ext u
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact hne_one u
  rw [hrw] at hsplit
  rw [hsplit, Finset.card_erase_of_mem hv]

/-- **Recurrence.** If `HasRamseyProperty Ns s (t+1)` and `HasRamseyProperty Nt (s+1) t`
hold, then `HasRamseyProperty (Ns + Nt) (s+1) (t+1)` holds.

This is the core Erdős–Szekeres 1935 pigeonhole step: pick any vertex `v ∈ V`, split
`V.erase v` into red-neighbours `R_v` and blue-neighbours `B_v`; by pigeonhole
`|R_v| ≥ Ns` or `|B_v| ≥ Nt`. In the first case, invoke `HasRamseyProperty Ns s (t+1)`
on `R_v`: either we get a red `K_s` on `R_v` (extend by `v` to a red `K_{s+1}` on `V`)
or a blue `K_{t+1}` on `R_v ⊆ V` (done). The second case is symmetric. -/
lemma HasRamseyProperty.step {Ns Nt s t : ℕ}
    (hs : HasRamseyProperty Ns s (t + 1))
    (ht : HasRamseyProperty Nt (s + 1) t) (hNs : 1 ≤ Ns) :
    HasRamseyProperty (Ns + Nt) (s + 1) (t + 1) := by
  classical
  intro n χ V hV
  -- V is nonempty since V.card ≥ Ns + Nt ≥ 1.
  have hVpos : 0 < V.card := by
    have : 1 ≤ V.card := Nat.le_trans hNs (Nat.le_trans (Nat.le_add_right _ _) hV)
    exact this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  -- Split V.erase v by colour of edge vu.
  set R := (V.erase v).filter (fun u => χ v u = 0) with hR_def
  set B := (V.erase v).filter (fun u => χ v u = 1) with hB_def
  have hsplit : R.card + B.card = V.card - 1 :=
    card_red_blue_split χ V hv
  have hRsubV : R ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsubV : B ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hvnR : v ∉ R := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  have hvnB : v ∉ B := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  -- Pigeonhole: either R.card ≥ Ns or B.card ≥ Nt.
  have hV' : V.card - 1 + 1 = V.card := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, hv⟩)
  by_cases hRcard : Ns ≤ R.card
  · -- Case 1: apply `hs` on R to get red K_s (extend by v) or blue K_{t+1}.
    rcases hs χ R hRcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- Red K_s on R ⊆ V; extend by v (red-adjacent to all of R) to red K_{s+1}.
      refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hRsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem (fun h => hvnR (hSsub h)), hScard]
      · apply hSmono.insert v (fun h => hvnR (hSsub h))
        intro u hu
        have hu' : u ∈ R := hSsub hu
        have : χ v u = 0 := (Finset.mem_filter.mp hu').2
        exact this
    · -- Blue K_{t+1} on R ⊆ V.
      exact Or.inr ⟨S, hSsub.trans hRsubV, hScard, hSmono⟩
  · -- Case 2: R.card < Ns, so B.card ≥ Nt. Apply `ht` on B symmetrically.
    push_neg at hRcard
    have hBcard : Nt ≤ B.card := by
      have hV_sub : Ns + Nt ≤ V.card := hV
      omega
    rcases ht χ B hBcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- Red K_{s+1} on B ⊆ V.
      exact Or.inl ⟨S, hSsub.trans hBsubV, hScard, hSmono⟩
    · -- Blue K_t on B; extend by v (blue-adjacent to all of B) to blue K_{t+1}.
      refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hBsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem (fun h => hvnB (hSsub h)), hScard]
      · apply hSmono.insert v (fun h => hvnB (hSsub h))
        intro u hu
        have hu' : u ∈ B := hSsub hu
        have : χ v u = 1 := (Finset.mem_filter.mp hu').2
        exact this

/-- **Binomial bound via Erdős–Szekeres induction.**
`HasRamseyProperty (Nat.choose (s + t) s) s t` for all `s, t`. -/
lemma hasRamseyProperty_choose : ∀ (s t : ℕ),
    HasRamseyProperty (Nat.choose (s + t) s) s t := by
  -- Induction on `s + t` via `Nat.strong_induction_on`.
  suffices h : ∀ (m : ℕ), ∀ (s t : ℕ), s + t = m → HasRamseyProperty (Nat.choose m s) s t by
    intro s t
    exact h (s + t) s t rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s t hst
    match s, t, hst with
    | 0, t, hst =>
      -- C(m, 0) = 1; we want HasRamseyProperty 1 0 t, which follows from the s = 0 base.
      show HasRamseyProperty (Nat.choose m 0) 0 t
      rw [Nat.choose_zero_right]
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_left 0 t)
    | s+1, 0, hst =>
      -- C(m, s+1) with t = 0. Use the t = 0 base case.
      show HasRamseyProperty (Nat.choose m (s+1)) (s+1) 0
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_right 0 (s+1))
    | s+1, t+1, hst =>
      -- Pascal: C(m, s+1) = C(m-1, s) + C(m-1, s+1), where m = s+1+t+1 = s+t+2.
      -- i.e. m - 1 = s + (t+1) = (s+1) + t.
      have hm : m = (s + 1) + (t + 1) := hst.symm
      have hm_pred : m - 1 + 1 = m := by omega
      have hm1 : m - 1 = s + (t + 1) := by omega
      have hm2 : m - 1 = (s + 1) + t := by omega
      have hs_ih : HasRamseyProperty (Nat.choose (m - 1) s) s (t + 1) := by
        apply ih (m - 1) (by omega) s (t + 1)
        omega
      have ht_ih : HasRamseyProperty (Nat.choose (m - 1) (s + 1)) (s + 1) t := by
        apply ih (m - 1) (by omega) (s + 1) t
        omega
      have hNs_pos : 1 ≤ Nat.choose (m - 1) s := by
        have : s ≤ m - 1 := by omega
        exact Nat.choose_pos this
      have hrec : HasRamseyProperty (Nat.choose (m - 1) s + Nat.choose (m - 1) (s + 1))
          (s + 1) (t + 1) := HasRamseyProperty.step hs_ih ht_ih hNs_pos
      -- Pascal's identity: C(m, s+1) = C(m-1, s) + C(m-1, s+1) when m ≥ 1.
      have hpascal : Nat.choose m (s + 1) = Nat.choose (m - 1) s + Nat.choose (m - 1) (s + 1) := by
        conv_lhs => rw [← hm_pred]
        rw [Nat.choose_succ_succ]
      show HasRamseyProperty (Nat.choose m (s + 1)) (s + 1) (t + 1)
      rw [hpascal]
      exact hrec

end Diagonal

/-- **Erdős–Szekeres 1935:** `R(k, k) ≤ 4 ^ k` for all `k`.

**Proof.** Use `Diagonal.hasRamseyProperty_choose` specialised to `s = t = k` to deduce
`IsRamsey (Nat.choose (2k) k) k`, yielding `ramseyNumber k ≤ C(2k, k)`; the central binomial
bound `C(2k, k) ≤ 4^k` closes the case `k ≥ 1`. The `k = 0` base case is immediate from
`ramseyNumber_zero = 0`. -/
lemma diagonal_ramsey_upper_bound (k : ℕ) :
    Diagonal.ramseyNumber k ≤ 4 ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Diagonal.ramseyNumber_zero]; exact Nat.zero_le _
  -- k ≥ 1. From `HasRamseyProperty (C(2k, k)) k k` we extract `IsRamsey (C(2k, k)) k`, so
  -- `ramseyNumber k ≤ C(2k, k) ≤ 4^k`.
  have hprop : Diagonal.HasRamseyProperty (Nat.choose (k + k) k) k k :=
    Diagonal.hasRamseyProperty_choose k k
  have hR : Diagonal.IsRamsey (Nat.choose (k + k) k) k := by
    intro χ
    -- Apply hprop with V = Finset.univ on Fin (C(2k, k)).
    have hV : Nat.choose (k + k) k ≤ (Finset.univ : Finset (Fin (Nat.choose (k + k) k))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
    rcases hprop χ Finset.univ hV with ⟨S, _hSsub, hScard, hSmono⟩ | ⟨S, _hSsub, hScard, hSmono⟩
    · exact ⟨S, 0, hScard, hSmono⟩
    · exact ⟨S, 1, hScard, hSmono⟩
  have hle : Diagonal.ramseyNumber k ≤ Nat.choose (k + k) k :=
    Nat.sInf_le hR
  have h2kk : Nat.choose (k + k) k = Nat.choose (2 * k) k := by
    rw [two_mul]
  rw [h2kk] at hle
  exact hle.trans (Diagonal.central_binomial_le_four_pow k)

/-! ## Bridge to `Combinatorics.hypergraphRamsey 2`

The Mathlib-style "binary diagonal Ramsey number" is `Combinatorics.hypergraphRamsey 2 k`
in `FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`, defined via a `Bool`-valued
coloring of `r`-element subsets of `Fin m`. Every `Diagonal.IsRamsey n k` witness can be
turned into membership of `n` in the `hypergraphRamsey 2 k` infimum set; chaining with
`hasRamseyProperty_choose` and `central_binomial_le_four_pow` we expose the headline bound
in the standard form.
-/

/-- Bridge: any `Diagonal.IsRamsey n k` witness yields membership of `n` in the
defining set of `Combinatorics.hypergraphRamsey 2 k`. -/
lemma _root_.Combinatorics.hypergraphRamsey_two_set_mem_of_isRamsey
    {n k : ℕ} (hR : Diagonal.IsRamsey n k) :
    n ∈ { m | ∀ (c : Finset (Fin m) → Bool), ∃ (S : Finset (Fin m)), S.card = k ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = 2 → c e = color } := by
  intro c
  -- Convert `c : Finset (Fin n) → Bool` to a `Diagonal.EdgeColouring n` (symmetric `Fin 2`).
  let χ : Diagonal.EdgeColouring n :=
    { toFun := fun i j => if c {i, j} then 0 else 1
      symm := fun i j => by simp [Finset.pair_comm] }
  obtain ⟨S, c', hScard, hSmono⟩ := hR χ
  refine ⟨S, hScard, decide (c' = 0), ?_⟩
  intro e heS hecard
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hecard
  have hu : u ∈ S := heS (Finset.mem_insert.mpr (Or.inl rfl))
  have hv : v ∈ S := heS (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  have hχuv : χ u v = c' := hSmono u hu v hv huv
  show c {u, v} = decide (c' = 0)
  by_cases hcuv : c {u, v}
  · have : χ u v = 0 := by simp [χ, hcuv]
    have hc'0 : c' = 0 := by rw [← hχuv, this]
    simp [hcuv, hc'0]
  · have : χ u v = 1 := by simp [χ, hcuv]
    have hc'1 : c' = 1 := by rw [← hχuv, this]
    simp [hcuv, hc'1]

/-- **Erdős–Szekeres 1935 in `hypergraphRamsey` form**:
`Combinatorics.hypergraphRamsey 2 k ≤ 4 ^ k`.

Composes the bridge `hypergraphRamsey_two_set_mem_of_isRamsey` (applied to the
`IsRamsey (C(2k,k)) k` witness extracted from `Diagonal.hasRamseyProperty_choose`) with
`Diagonal.central_binomial_le_four_pow`. This is the "Mathlib-shaped" version of the result. -/
lemma _root_.Combinatorics.hypergraphRamsey_two_le_four_pow (k : ℕ) :
    Combinatorics.hypergraphRamsey 2 k ≤ 4 ^ k := by
  -- Build IsRamsey (C(2k,k)) k from hasRamseyProperty_choose, mirroring diagonal_ramsey_upper_bound.
  have hprop : Diagonal.HasRamseyProperty (Nat.choose (k + k) k) k k :=
    Diagonal.hasRamseyProperty_choose k k
  have hR : Diagonal.IsRamsey (Nat.choose (k + k) k) k := by
    intro χ
    have hV : Nat.choose (k + k) k ≤ (Finset.univ : Finset (Fin (Nat.choose (k + k) k))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
    rcases hprop χ Finset.univ hV with ⟨S, _hSsub, hScard, hSmono⟩ | ⟨S, _hSsub, hScard, hSmono⟩
    · exact ⟨S, 0, hScard, hSmono⟩
    · exact ⟨S, 1, hScard, hSmono⟩
  -- Bridge to hypergraphRamsey set membership and apply Nat.sInf_le.
  have hmem := Combinatorics.hypergraphRamsey_two_set_mem_of_isRamsey hR
  have hle : Combinatorics.hypergraphRamsey 2 k ≤ Nat.choose (k + k) k := Nat.sInf_le hmem
  have h2kk : Nat.choose (k + k) k = Nat.choose (2 * k) k := by rw [two_mul]
  rw [h2kk] at hle
  exact hle.trans (Diagonal.central_binomial_le_four_pow k)

end Combinatorics

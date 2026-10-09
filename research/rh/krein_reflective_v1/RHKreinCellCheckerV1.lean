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

import RHKreinTrigTMV1
import RHKreinRotTMV1
import RHKreinHatFastV1
import RHKreinSymbolLowerQV1
import RHKreinCellAnalyticBridgeV1

/-!
# Reflective cell checker for the order-19 Krein certificate

`checkCell pa c breaks` is a Boolean computation over `ℚ`.  It splits the cell
`[c.lo, c.hi]` at `breaks`, builds on every piece a rational Taylor model of

  `correctionSymbol t + (t² + 1/4)² · (symbolFloor t - 1/16 - lowerValue c)`,

(`symbolFloor` from `RHKreinSymbolLowerQV1`), and checks that its floor exceeds its error.
`checkCell_sound` turns `checkCell pa c breaks = true` into `CellAnalyticSoundV1 c`; a closed
instance is discharged by `decide +kernel`.

No RH statement is concluded.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCellCheckerV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinRotTMV1
open AEGIS.RHKreinHatFastV1
open AEGIS.RHKreinSymbolLowerQV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinCellAnalyticBridgeV1

structure Params where
  q : TrigParams
  K : ℕ
  P : ℕ
  D : ℕ

/-! ## Hat sum -/

def hcN (n : ℕ) : ℚ := if h : n < 199 then hatCoefficient ⟨n, h⟩ else 0
def hN (n : ℕ) : ℚ := ((n : ℚ) + 41) / 50

/-- Running hat polynomial, error, and the phase `exp (i c hN n)`, advanced by one rotation per
column.  The rows share the denominators `50ᵐ m!`, so no rounding is needed inside the sum. -/
def hatAcc (pa : Params) (r c : ℚ) (B : CS) : ℕ → Poly × ℚ × CS
  | 0 => ([], 0, phaseZ pa.q.nb pa.q.k pa.P (c * hN 0))
  | n + 1 =>
    match hatAcc pa r c B n with
    | (p, e, A) =>
      if 0 < pa.q.n ∧ r * |hN n| ≤ 1 then
        (padd p (psmul (hcN n) (phaseRow A.c A.s (hN n) 0 pa.q.n 1)),
          e + |hcN n| * colErr pa.q.n r (hN n) A, rotC pa.P A B)
      else (p, e + |hcN n|, rotC pa.P A B)

def hatTM (pa : Params) (r c : ℚ) (N : ℕ) : TM :=
  match hatAcc pa r c (phaseZ pa.q.nb pa.q.k pa.P (c / 50)) N with
  | (p, e, _) => TM.trim pa.P pa.D r ⟨p, e⟩

theorem hatAcc_spec (pa : Params) (r c : ℚ) (hr : 0 ≤ r) (B : CS)
    (hB : ZEncl ((c / 50 : ℚ) : ℝ) B) :
    ∀ N : ℕ, Encl r (fun s => ∑ n ∈ Finset.range N,
      (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ)))
        ⟨(hatAcc pa r c B N).1, (hatAcc pa r c B N).2.1⟩ ∧
      ZEncl ((c * hN N : ℚ) : ℝ) (hatAcc pa r c B N).2.2
  | 0 => by
    refine ⟨?_, phaseZ_encl _ _ _ _⟩
    intro s _; simp [hatAcc]
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := hatAcc_spec pa r c hr B hB N
    have hrot : ZEncl ((c * hN (N + 1) : ℚ) : ℝ) (rotC pa.P (hatAcc pa r c B N).2.2 B) := by
      have := rotC_encl pa.P ih2 hB
      have e : ((c * hN N : ℚ) : ℝ) + ((c / 50 : ℚ) : ℝ) = ((c * hN (N + 1) : ℚ) : ℝ) := by
        unfold hN; push_cast; ring
      rwa [e] at this
    rcases h0 : hatAcc pa r c B N with ⟨p, e, A⟩
    rw [h0] at ih1 ih2 hrot
    simp only [hatAcc, h0]
    split_ifs with hc
    · refine ⟨?_, hrot⟩
      intro s hs
      have h1 := ih1 s hs
      have h2 := col_encl pa.q.n r c (hN N) hr hc.1 hc.2 A ih2 s hs
      simp only [eval_padd, eval_psmul, Finset.sum_range_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e2 : (∑ n ∈ Finset.range N, (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ))) +
          (hcN N : ℝ) * Real.cos (((c : ℝ) + s) * (hN N : ℝ)) -
          (eval p s + (hcN N : ℝ) * eval (phaseRow A.c A.s (hN N) 0 pa.q.n 1) s) =
          ((∑ n ∈ Finset.range N, (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ))) - eval p s) +
          (hcN N : ℝ) * (Real.cos (((c : ℝ) + s) * (hN N : ℝ)) -
            eval (phaseRow A.c A.s (hN N) 0 pa.q.n 1) s) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans (add_le_add h1 ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (abs_nonneg _)
    · refine ⟨?_, hrot⟩
      intro s hs
      have h1 := ih1 s hs
      simp only [Finset.sum_range_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e2 : (∑ n ∈ Finset.range N, (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ))) +
          (hcN N : ℝ) * Real.cos (((c : ℝ) + s) * (hN N : ℝ)) - eval p s =
          ((∑ n ∈ Finset.range N, (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ))) - eval p s) +
          (hcN N : ℝ) * Real.cos (((c : ℝ) + s) * (hN N : ℝ)) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans (add_le_add h1 ?_)
      rw [abs_mul]
      calc |(hcN N : ℝ)| * |Real.cos (((c : ℝ) + s) * (hN N : ℝ))| ≤ |(hcN N : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |(hcN N : ℝ)| := mul_one _

theorem encl_hat (pa : Params) (r c : ℚ) (hr : 0 ≤ r) (N : ℕ) :
    Encl r (fun s => ∑ n ∈ Finset.range N,
      (hcN n : ℝ) * Real.cos (((c : ℝ) + s) * (hN n : ℝ))) (hatTM pa r c N) := by
  have h := (hatAcc_spec pa r c hr _ (phaseZ_encl pa.q.nb pa.q.k pa.P (c / 50)) N).1
  unfold hatTM
  rcases h0 : hatAcc pa r c (phaseZ pa.q.nb pa.q.k pa.P (c / 50)) N with ⟨p, e, A⟩
  rw [h0] at h
  exact Encl.trim hr h pa.P pa.D

theorem hat_sum_eq (t : ℝ) :
    (∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)) =
      ∑ n ∈ Finset.range 199, (hcN n : ℝ) * Real.cos (t * (hN n : ℝ)) := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => (hcN n : ℝ) * Real.cos (t * (hN n : ℝ)))]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : hcN j.val = hatCoefficient j := by
    unfold hcN; rw [dif_pos j.isLt]
  rw [h1]
  unfold hN hatCenter
  push_cast; ring_nf

/-! ## Edge sum -/

def splQ (i : ℕ) : ℚ := if h : i < 5 then splineCoefficient ⟨i, h⟩ else 0

def tVar (c : ℚ) : TM := ⟨[c, 1], 0⟩

theorem encl_tVar (r c : ℚ) : Encl r (fun s => (c : ℝ) + s) (tVar c) := by
  intro s _; simp [tVar]

def edgeTM (pa : Params) (r c : ℚ) : TM :=
  let C := cosAffTM pa.q r c (1619 / 2000)
  let S := sinAffTM pa.q r c (1619 / 2000)
  let T := tVar c
  let T2 := TM.mul r T T
  let T3 := TM.mul r T2 T
  let T4 := TM.mul r T2 T2
  TM.trim pa.P pa.D r
    (TM.add (TM.add (TM.add (TM.add (TM.smul (splQ 0) C)
      (TM.smul (splQ 1) (TM.mul r T S)))
      (TM.smul (splQ 2) (TM.mul r T2 C)))
      (TM.smul (splQ 3) (TM.mul r T3 S)))
      (TM.smul (splQ 4) (TM.mul r T4 C)))

theorem encl_edge (pa : Params) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => ∑ j : Fin 5, (splineCoefficient j : ℝ) * ((c : ℝ) + s) ^ j.val *
      (if j.val % 2 = 0 then Real.cos (((c : ℝ) + s) * (1619 / 2000))
       else Real.sin (((c : ℝ) + s) * (1619 / 2000)))) (edgeTM pa r c) := by
  have hC := encl_cosAff pa.q r c (1619 / 2000) hr
  have hS := encl_sinAff pa.q r c (1619 / 2000) hr
  have hT := encl_tVar r c
  have hT2 := Encl.mul hr hT hT
  have hT3 := Encl.mul hr hT2 hT
  have hT4 := Encl.mul hr hT2 hT2
  have h := Encl.trim hr (Encl.add (Encl.add (Encl.add (Encl.add (Encl.smul (splQ 0) hC)
    (Encl.smul (splQ 1) (Encl.mul hr hT hS)))
    (Encl.smul (splQ 2) (Encl.mul hr hT2 hC)))
    (Encl.smul (splQ 3) (Encl.mul hr hT3 hS)))
    (Encl.smul (splQ 4) (Encl.mul hr hT4 hC))) pa.P pa.D
  refine Encl.congr h ?_
  intro s _
  simp only [Fin.sum_univ_five, splQ]
  norm_num
  push_cast
  ring

/-! ## The margin model -/

def weightTM (r c : ℚ) : TM :=
  let T := tVar c
  let B := TM.add (TM.mul r T T) (TM.const (1 / 4))
  TM.mul r B B

theorem encl_weight (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => (((c : ℝ) + s) ^ 2 + 1 / 4) ^ 2) (weightTM r c) := by
  have hT := encl_tVar r c
  have hB := Encl.add (Encl.mul hr hT hT) (Encl.const r (1 / 4))
  refine Encl.congr (Encl.mul hr hB hB) ?_
  intro s _; push_cast; ring

/-- `symbolFloor t - 1/16 - lv` as a Taylor model. -/
def slackTM (pa : Params) (r c lo lv : ℚ) : TM :=
  TM.sub (TM.sub (TM.const (archLQ lo - 1 / 16 - lv - 2 / 10 ^ 9))
    (TM.smul A0 (cosAffTM pa.q r c L0)))
    (TM.smul (A0 / 10 ^ 10) (tVar c))

theorem encl_slack (pa : Params) (r c lo lv : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => (archLQ lo : ℝ) - A0 * Real.cos (((c : ℝ) + s) * L0) -
      A0 * ((c : ℝ) + s) / 10 ^ 10 - 2 / 10 ^ 9 - 1 / 16 - lv) (slackTM pa r c lo lv) := by
  have h := Encl.sub (Encl.sub (Encl.const r (archLQ lo - 1 / 16 - lv - 2 / 10 ^ 9))
    (Encl.smul A0 (encl_cosAff pa.q r c L0 hr)))
    (Encl.smul (A0 / 10 ^ 10) (encl_tVar r c))
  refine Encl.congr h ?_
  intro s _; push_cast; ring

def tmSq (r : ℚ) (P D : ℕ) (T : TM) : TM := TM.trim P D r (TM.mul r T T)

def pow19 (r : ℚ) (P D : ℕ) (T : TM) : TM :=
  let T2 := tmSq r P D T
  let T4 := tmSq r P D T2
  let T8 := tmSq r P D T4
  let T16 := tmSq r P D T8
  TM.trim P D r (TM.mul r (TM.trim P D r (TM.mul r T16 T2)) T)

theorem encl_pow19 {r : ℚ} (hr : 0 ≤ r) (P D : ℕ) {f : ℝ → ℝ} {T : TM} (hf : Encl r f T) :
    Encl r (fun s => f s ^ 19) (pow19 r P D T) := by
  have h2 := Encl.trim hr (Encl.mul hr hf hf) P D
  have h4 := Encl.trim hr (Encl.mul hr h2 h2) P D
  have h8 := Encl.trim hr (Encl.mul hr h4 h4) P D
  have h16 := Encl.trim hr (Encl.mul hr h8 h8) P D
  have h18 := Encl.trim hr (Encl.mul hr h16 h2) P D
  have h19 := Encl.trim hr (Encl.mul hr h18 hf) P D
  refine Encl.congr h19 ?_
  intro s _; ring

def marginTM (pa : Params) (lo lv a b : ℚ) : TM :=
  let c := (a + b) / 2
  let r := (b - a) / 2
  let S1 := sincAffTM pa.q pa.K r c 100
  let S2 := sincAffTM pa.q pa.K r c 2000
  let corr := TM.add (TM.smul (2 / 50) (TM.mul r (tmPow r pa.P pa.D S1 2) (hatTM pa r c 199)))
    (TM.mul r (pow19 r pa.P pa.D S2) (edgeTM pa r c))
  TM.add corr (TM.mul r (weightTM r c) (slackTM pa r c lo lv))

theorem encl_margin (pa : Params) (lo lv a b : ℚ) (hab : a ≤ b) :
    Encl ((b - a) / 2) (fun s =>
      correctionSymbol ((((a + b) / 2 : ℚ) : ℝ) + s) +
        (((((a + b) / 2 : ℚ) : ℝ) + s) ^ 2 + 1 / 4) ^ 2 *
          ((archLQ lo : ℝ) - A0 * Real.cos (((((a + b) / 2 : ℚ) : ℝ) + s) * L0) -
            A0 * ((((a + b) / 2 : ℚ) : ℝ) + s) / 10 ^ 10 - 2 / 10 ^ 9 - 1 / 16 - lv))
      (marginTM pa lo lv a b) := by
  set c : ℚ := (a + b) / 2
  set r : ℚ := (b - a) / 2
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hS1 := encl_tmPow hr pa.P pa.D (encl_sincAff pa.q pa.K r c 100) 2
  have hS2 := encl_pow19 hr pa.P pa.D (encl_sincAff pa.q pa.K r c 2000)
  have hH := encl_hat pa r c hr 199
  have hE := encl_edge pa r c hr
  have hcorr := Encl.add (Encl.smul (2 / 50) (Encl.mul hr hS1 hH)) (Encl.mul hr hS2 hE)
  have h := Encl.add hcorr (Encl.mul hr (encl_weight r c hr) (encl_slack pa r c lo lv hr))
  refine Encl.congr h ?_
  intro s _
  unfold correctionSymbol
  rw [hat_sum_eq]
  push_cast
  ring

/-! ## Pieces and cells -/

def checkPiece (pa : Params) (lo lv a b : ℚ) : Bool :=
  decide (0 < lo) && decide (lo ≤ a) && decide (a ≤ b) &&
    (let M := marginTM pa lo lv a b
     decide (M.e ≤ floorBound M.p ((b - a) / 2)))

/-- The exact budget consumed by `cellAnalyticSound_of_correction_lower` with the identity
correction lower bound. -/
def Budget (lv : ℚ) (t : ℝ) : Prop :=
  (t ^ 2 + 1 / 4) ^ 2 * (lv : ℝ) ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) + correctionSymbol t

theorem checkPiece_sound (pa : Params) (lo lv a b : ℚ) (h : checkPiece pa lo lv a b = true) :
    ∀ t : ℝ, (a : ℝ) ≤ t → t ≤ b → Budget lv t := by
  simp only [checkPiece, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo0, hloa⟩, hab⟩, hM⟩ := h
  intro t hat htb
  have hr : (0 : ℚ) ≤ (b - a) / 2 := by linarith
  have hE := encl_margin pa lo lv a b hab
  have hnn := Encl.nonneg hr hE hM (t - (((a + b) / 2 : ℚ) : ℝ)) (by
    rw [abs_le]; push_cast; constructor <;> linarith)
  simp only [add_sub_cancel] at hnn
  have hsym := symbol_lower lo t (by exact_mod_cast hlo0.le)
    (le_trans (by exact_mod_cast hloa) hat)
  have hW : (0 : ℝ) ≤ (t ^ 2 + 1 / 4) ^ 2 := by positivity
  unfold Budget
  have := mul_le_mul_of_nonneg_left (sub_le_sub_right (sub_le_sub_right hsym (1 / 16)) (lv : ℝ)) hW
  nlinarith

def checkChain (pa : Params) (lo lv hi : ℚ) : ℚ → List ℚ → Bool
  | a, [] => decide (a = hi)
  | a, b :: rest => checkPiece pa lo lv a b && checkChain pa lo lv hi b rest

theorem checkChain_sound (pa : Params) (lo lv hi : ℚ) :
    ∀ (l : List ℚ) (a : ℚ), checkChain pa lo lv hi a l = true →
      ∀ t : ℝ, (a : ℝ) < t → t ≤ hi → Budget lv t
  | [], a, h, t, hat, hth => by
    simp only [checkChain, decide_eq_true_eq] at h
    subst h; exact absurd hth (not_le.mpr hat)
  | b :: rest, a, h, t, hat, hth => by
    simp only [checkChain, Bool.and_eq_true] at h
    by_cases htb : t ≤ b
    · exact checkPiece_sound pa lo lv a b h.1 t hat.le htb
    · exact checkChain_sound pa lo lv hi rest b h.2 t (not_le.mp htb) hth

def checkCell (pa : Params) (c : FiniteCellV1) : List ℚ → Bool
  | [] => false
  | b :: rest => checkPiece pa c.lo (lowerValue c) c.lo b &&
      checkChain pa c.lo (lowerValue c) c.hi b rest

theorem checkCell_sound (pa : Params) (c : FiniteCellV1) (l : List ℚ)
    (h : checkCell pa c l = true) : CellAnalyticSoundV1 c := by
  have hall : ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) → Budget (lowerValue c) t := by
    cases l with
    | nil => simp [checkCell] at h
    | cons b rest =>
      simp only [checkCell, Bool.and_eq_true] at h
      intro t hlo hhi
      by_cases htb : t ≤ b
      · exact checkPiece_sound pa c.lo (lowerValue c) c.lo b h.1 t hlo htb
      · exact checkChain_sound pa c.lo (lowerValue c) c.hi rest b h.2 t (not_le.mp htb) hhi
  apply cellAnalyticSound_of_correction_lower c correctionSymbol
  · intro t _ _; exact le_refl _
  · intro t hlo hhi; exact hall t hlo hhi

end AEGIS.RHKreinCellCheckerV1

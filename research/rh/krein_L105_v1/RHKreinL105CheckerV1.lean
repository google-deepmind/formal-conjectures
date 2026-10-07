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

import RHKreinL105TMV1
import RHKreinDigammaSharpTailV1
import RHKreinSymbolConstQV1

/-!
# Reflective checker for the `L = 21/20` Krein certificate

The certificate function is

  `Fcert t = (t² + 1/4)² · symbol t + (2/50) sinc(t/100)² Σ_k c_k cos(t u_k) + Σ_j d_j tʲ cs_j(t L)`

with `u_k = 21/20 + (k+1)/50`, `L = 21/20`, `cs_j = cos` (`j` even) or `sin` (`j` odd).

`checkWide pa K₀ hats lo hi breaks` builds ONE Taylor model on the wide cell `[lo, hi]` (centre `0`
when `lo = 0`).  Each piece `[a, b]` of `breaks` re-centres that polynomial and adds
`W · midLower a`, the monotone constant for the digamma terms `n ≥ K₀` with the sharp telescoping
tail.  `checkWide_sound` gives `0 ≤ Fcert t` on `[lo, hi]`.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinL105CheckerV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinRotTMV1
open AEGIS.RHKreinHatFastV1
open AEGIS.RHKreinL105TMV1
open AEGIS.RHKreinL105DataV1
open AEGIS.RHKreinSymbolConstQV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinDigammaSharpTailV1

def tVar (c : ℚ) : TM := ⟨[c, 1], 0⟩

theorem encl_tVar (r c : ℚ) : Encl r (fun s => (c : ℝ) + s) (tVar c) := by
  intro s _; simp [tVar]

structure Params where
  q : TrigParams
  D : ℕ
  K : ℕ
  N : ℕ

def L105 : ℚ := 21 / 20

def dq (j : ℕ) : ℚ := dqList.getD j 0

def deltaFun (t : ℝ) : ℝ :=
  (dq 0 : ℝ) * Real.cos (t * L105) + (dq 1 : ℝ) * t * Real.sin (t * L105) +
    (dq 2 : ℝ) * t ^ 2 * Real.cos (t * L105) + (dq 3 : ℝ) * t ^ 3 * Real.sin (t * L105) +
    (dq 4 : ℝ) * t ^ 4 * Real.cos (t * L105)

def hatFun (t : ℝ) : ℝ := 2 / 50 * Real.sinc (t / 100) ^ 2 * hatSumL cqList (107 / 100) t

def Fcert (t : ℝ) : ℝ := (t ^ 2 + 1 / 4) ^ 2 * symbol t + hatFun t + deltaFun t

/-! ## Components -/

def deltaTM (pa : Params) (r c : ℚ) : TM :=
  let C := cosAffTM pa.q r c L105
  let S := sinAffTM pa.q r c L105
  let T := tVar c
  let T2 := TM.mul r T T
  let T3 := TM.mul r T2 T
  let T4 := TM.mul r T2 T2
  TM.trim pa.q.P pa.D r
    (TM.add (TM.add (TM.add (TM.add (TM.smul (dq 0) C)
      (TM.smul (dq 1) (TM.mul r T S)))
      (TM.smul (dq 2) (TM.mul r T2 C)))
      (TM.smul (dq 3) (TM.mul r T3 S)))
      (TM.smul (dq 4) (TM.mul r T4 C)))

theorem encl_delta (pa : Params) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => deltaFun ((c : ℝ) + s)) (deltaTM pa r c) := by
  have hC := encl_cosAff pa.q r c L105 hr
  have hS := encl_sinAff pa.q r c L105 hr
  have hT := encl_tVar r c
  have hT2 := Encl.mul hr hT hT
  have hT3 := Encl.mul hr hT2 hT
  have hT4 := Encl.mul hr hT2 hT2
  have h := Encl.trim hr (Encl.add (Encl.add (Encl.add (Encl.add (Encl.smul (dq 0) hC)
    (Encl.smul (dq 1) (Encl.mul hr hT hS)))
    (Encl.smul (dq 2) (Encl.mul hr hT2 hC)))
    (Encl.smul (dq 3) (Encl.mul hr hT3 hS)))
    (Encl.smul (dq 4) (Encl.mul hr hT4 hC))) pa.q.P pa.D
  refine Encl.congr h ?_
  intro s _
  unfold deltaFun
  ring

def GAMMA_U : ℚ := 5773 / 10000
def LOGPI_U : ℚ := 1144729886 / 1000000000

def symTM (pa : Params) (K0 : ℕ) (r c : ℚ) : TM :=
  TM.sub (TM.sub (TM.add (headTM K0 pa.D r c K0) (TM.const (-GAMMA_U - LOGPI_U - 2 / 10 ^ 9)))
    (TM.smul A0 (cosAffTM pa.q r c L0))) (TM.smul (A0 / 10 ^ 10) (tVar c))

def symFun (K0 : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.range K0, quarterTerm t n) + (-GAMMA_U - LOGPI_U - 2 / 10 ^ 9 : ℚ) -
    A0 * Real.cos (t * L0) - A0 / 10 ^ 10 * t

theorem encl_sym (pa : Params) (K0 : ℕ) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => symFun K0 ((c : ℝ) + s)) (symTM pa K0 r c) := by
  have h := Encl.sub (Encl.sub (Encl.add (encl_headTM K0 pa.D r c hr K0 le_rfl)
    (Encl.const r (-GAMMA_U - LOGPI_U - 2 / 10 ^ 9)))
    (Encl.smul A0 (encl_cosAff pa.q r c L0 hr))) (Encl.smul (A0 / 10 ^ 10) (encl_tVar r c))
  refine Encl.congr h ?_
  intro s _
  unfold symFun
  push_cast
  ring

def sincTM (pa : Params) (r c : ℚ) : TM :=
  if c = 0 then sincZeroTM pa.q.n r 100 else sincAffTM pa.q pa.K r c 100

theorem encl_sincTM (pa : Params) (r c : ℚ) :
    Encl r (fun s => Real.sinc (((c : ℝ) + s) / 100)) (sincTM pa r c) := by
  unfold sincTM
  split_ifs with hc
  · subst hc
    refine Encl.congr (encl_sincZero pa.q.n r 100) ?_
    intro s _; push_cast; simp
  · exact encl_sincAff pa.q pa.K r c 100

def hatTM (pa : Params) (r c : ℚ) : TM :=
  let A := phaseZ pa.q.nb pa.q.k pa.q.P (c * (107 / 100))
  let B := phaseZ pa.q.nb pa.q.k pa.q.P (c / 50)
  let R := hatAccL pa.q.n pa.q.P r B cqList (107 / 100) A [] 0
  TM.trim pa.q.P pa.D r ⟨R.1, R.2⟩

theorem encl_hatTM (pa : Params) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => hatSumL cqList (107 / 100) ((c : ℝ) + s)) (hatTM pa r c) := by
  have h0 : Encl r (fun _ => (0 : ℝ)) ⟨[], 0⟩ := by intro s _; simp
  have h := hatAccL_spec pa.q.n pa.q.P r c hr _ (phaseZ_encl pa.q.nb pa.q.k pa.q.P (c / 50))
    cqList (107 / 100) _ [] 0 _ (phaseZ_encl pa.q.nb pa.q.k pa.q.P (c * (107 / 100))) h0
  have h2 := Encl.trim hr h pa.q.P pa.D
  refine Encl.congr h2 ?_
  intro s _; simp

def hatPart (pa : Params) (hats : Bool) (r c : ℚ) : TM :=
  if hats then TM.smul (2 / 50) (TM.mul r (tmPow r pa.q.P pa.D (sincTM pa r c) 2) (hatTM pa r c))
  else hatBallTM (absSum cqList) r c

theorem encl_hatPart (pa : Params) (hats : Bool) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => hatFun ((c : ℝ) + s)) (hatPart pa hats r c) := by
  unfold hatPart hatFun
  split_ifs with hh
  · have h := Encl.smul (2 / 50) (Encl.mul hr
      (encl_tmPow hr pa.q.P pa.D (encl_sincTM pa r c) 2) (encl_hatTM pa r c hr))
    refine Encl.congr h ?_
    intro s _; push_cast; ring
  · exact encl_hatBall cqList (107 / 100) r c

def weightPoly (c : ℚ) : Poly := pmul [c ^ 2 + 1 / 4, 2 * c, 1] [c ^ 2 + 1 / 4, 2 * c, 1]

theorem eval_weightPoly (c : ℚ) (s : ℝ) :
    eval (weightPoly c) s = (((c : ℝ) + s) ^ 2 + 1 / 4) ^ 2 := by
  simp only [weightPoly, eval_pmul, eval_cons, eval_nil]; push_cast; ring

def wideTM (pa : Params) (K0 : ℕ) (hats : Bool) (r c : ℚ) : TM :=
  TM.trim pa.q.P pa.D r (TM.add (TM.add (hatPart pa hats r c) (deltaTM pa r c))
    (TM.mul r ⟨weightPoly c, 0⟩ (symTM pa K0 r c)))

def wideFun (K0 : ℕ) (t : ℝ) : ℝ :=
  hatFun t + deltaFun t + (t ^ 2 + 1 / 4) ^ 2 * symFun K0 t

theorem encl_wide (pa : Params) (K0 : ℕ) (hats : Bool) (r c : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => wideFun K0 ((c : ℝ) + s)) (wideTM pa K0 hats r c) := by
  have hW : Encl r (fun s => (((c : ℝ) + s) ^ 2 + 1 / 4) ^ 2) ⟨weightPoly c, 0⟩ := by
    intro s _; simp [eval_weightPoly]
  have h := Encl.trim hr (Encl.add (Encl.add (encl_hatPart pa hats r c hr) (encl_delta pa r c hr))
    (Encl.mul hr hW (encl_sym pa K0 r c hr))) pa.q.P pa.D
  refine Encl.congr h ?_
  intro s _; unfold wideFun; ring

/-! ## The monotone digamma constant -/

def midSum (P : ℕ) (a : ℚ) : ℕ → ℕ → ℚ
  | _, 0 => 0
  | k, m + 1 => roundQ P (quarterTermQ a k) + midSum P a (k + 1) m

def midLower (P K0 N : ℕ) (a : ℚ) : ℚ :=
  midSum P a K0 (N - K0) - 3 / 4 * (1 / ((N : ℚ) + 1 / 4) + 1 / ((N : ℚ) + 1 / 4) ^ 2) +
    (a ^ 2 / 4) / (2 * ((N : ℚ) + 1 / 4) ^ 2 + a ^ 2 / 4)

theorem roundQ_le (k : ℕ) (q : ℚ) : roundQ k q ≤ q := by
  unfold roundQ
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem quarterTermQ_cast (a : ℚ) (n : ℕ) : ((quarterTermQ a n : ℚ) : ℝ) = quarterTerm a n := by
  simp only [quarterTermQ, quarterTerm]; push_cast; ring

theorem midSum_le (P : ℕ) (a : ℚ) (t : ℝ) (hst : (a : ℝ) ^ 2 ≤ t ^ 2) :
    ∀ (m k : ℕ), ((midSum P a k m : ℚ) : ℝ) ≤ ∑ i ∈ Finset.range m, quarterTerm t (k + i)
  | 0, k => by simp [midSum]
  | m + 1, k => by
    simp only [midSum]
    rw [Finset.sum_range_succ']
    have ih := midSum_le P a t hst m (k + 1)
    have h1 : ((roundQ P (quarterTermQ a k) : ℚ) : ℝ) ≤ quarterTerm t k := by
      have := roundQ_le P (quarterTermQ a k)
      have h2 : ((roundQ P (quarterTermQ a k) : ℚ) : ℝ) ≤ ((quarterTermQ a k : ℚ) : ℝ) := by
        exact_mod_cast this
      rw [quarterTermQ_cast] at h2
      exact h2.trans (quarterTerm_mono_of_sq_le _ _ hst k)
    push_cast
    have e : ∑ i ∈ Finset.range m, quarterTerm t (k + (i + 1)) =
        ∑ i ∈ Finset.range m, quarterTerm t (k + 1 + i) := by
      apply Finset.sum_congr rfl; intro i _; rw [show k + (i + 1) = k + 1 + i by omega]
    rw [e]; simp only [add_zero]; linarith

theorem symbol_lower105 (P K0 N : ℕ) (hKN : K0 ≤ N) (a : ℚ) (t : ℝ) (ha : (0 : ℝ) ≤ a)
    (hat : (a : ℝ) ≤ t) :
    symFun K0 t + (midLower P K0 N a : ℝ) ≤ symbol t := by
  have hst : (a : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
  have hsharp := digamma_quarter_sharp_lower t N
  unfold quarterPoint at hsharp
  have hsplit : (∑ n ∈ Finset.range N, quarterTerm t n) =
      (∑ n ∈ Finset.range K0, quarterTerm t n) +
        ∑ i ∈ Finset.range (N - K0), quarterTerm t (K0 + i) := by
    rw [← Finset.sum_range_add_sum_Ico _ hKN, Finset.sum_Ico_eq_sum_range]
  have hmid := midSum_le P a t hst (N - K0) K0
  have hphi : ((a : ℝ) ^ 2 / 4) / (2 * ((N : ℝ) + 1 / 4) ^ 2 + (a : ℝ) ^ 2 / 4) ≤
      (t ^ 2 / 4) / (2 * ((N : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by
    have h1 : 0 < 2 * ((N : ℝ) + 1 / 4) ^ 2 + (a : ℝ) ^ 2 / 4 := by positivity
    have h2 : 0 < 2 * ((N : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by positivity
    rw [div_le_div_iff₀ h1 h2]
    have h3 : 0 ≤ 2 * ((N : ℝ) + 1 / 4) ^ 2 := by positivity
    nlinarith
  have hg := AEGIS.RHEulerGammaSharpBaseV1.gamma_lt_5773
  have hlp := logPi_upper
  have hamp := amp_close
  have hl2 := log2_close
  have hA0 : (0 : ℝ) ≤ A0 := by unfold A0; positivity
  have ht0 : 0 ≤ t := ha.trans hat
  have hcos : |Real.cos (t * Real.log 2) - Real.cos (t * L0)| ≤ t / 10 ^ 10 := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg ht0]
    calc t * |Real.log 2 - (L0 : ℝ)| ≤ t * (1 / 10 ^ 10) :=
          mul_le_mul_of_nonneg_left hl2 ht0
      _ = t / 10 ^ 10 := by ring
  have hc1 : (A0 : ℝ) * Real.cos (t * Real.log 2) ≤ A0 * Real.cos (t * L0) + A0 * (t / 10 ^ 10) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hA0
    linarith [le_abs_self (Real.cos (t * Real.log 2) - Real.cos (t * L0))]
  have hc2 : (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) ≤ 2 / 10 ^ 9 := by
    calc (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) ≤
        |(Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2)| := le_abs_self _
      _ = |Real.sqrt 2 * Real.log 2 - A0| * |Real.cos (t * Real.log 2)| := abs_mul _ _
      _ ≤ (2 / 10 ^ 9) * 1 :=
          mul_le_mul hamp (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ = 2 / 10 ^ 9 := by ring
  unfold symbol archSymbol symFun midLower GAMMA_U LOGPI_U
  push_cast
  rw [hsplit] at hsharp
  have e : Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2) =
      A0 * Real.cos (t * Real.log 2) +
        (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) := by ring
  rw [e]
  push_cast at hmid
  linarith

/-! ## Pieces and wide cells -/

def pieceTot (pa : Params) (K0 : ℕ) (c : ℚ) (M : TM) (a b : ℚ) : Poly :=
  let h := (a + b) / 2 - c
  padd (shiftPoly h M.p) (psmul (midLower pa.q.P K0 pa.N a) (shiftPoly h (weightPoly c)))

def checkPiece (pa : Params) (K0 : ℕ) (c r : ℚ) (M : TM) (a b : ℚ) : Bool :=
  decide (0 ≤ a) && decide (a ≤ b) && decide (c - r ≤ a) && decide (b ≤ c + r) &&
    decide (K0 ≤ pa.N) && decide (M.e ≤ floorBound (pieceTot pa K0 c M a b) ((b - a) / 2))

theorem checkPiece_sound (pa : Params) (K0 : ℕ) (hats : Bool) (c r a b : ℚ) (hr : 0 ≤ r)
    (h : checkPiece pa K0 c r (wideTM pa K0 hats r c) a b = true) :
    ∀ t : ℝ, (a : ℝ) ≤ t → t ≤ b → 0 ≤ Fcert t := by
  simp only [checkPiece, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha0, hab⟩, hca⟩, hbc⟩, hKN⟩, hM⟩ := h
  intro t hat htb
  set M := wideTM pa K0 hats r c
  have hca' : ((c - r : ℚ) : ℝ) ≤ a := by exact_mod_cast hca
  have hbc' : (b : ℝ) ≤ ((c + r : ℚ) : ℝ) := by exact_mod_cast hbc
  push_cast at hca' hbc'
  have hs : |t - c| ≤ r := by rw [abs_le]; constructor <;> linarith
  have hE := encl_wide pa K0 hats r c hr (t - c) hs
  simp only [add_sub_cancel] at hE
  have hrho : (0 : ℚ) ≤ (b - a) / 2 := by linarith
  have hs' : |t - (((a + b) / 2 : ℚ) : ℝ)| ≤ (((b - a) / 2 : ℚ) : ℝ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have hfl := floorBound_le ((b - a) / 2) hrho (t - (((a + b) / 2 : ℚ) : ℝ)) hs'
    (pieceTot pa K0 c M a b)
  have hev : eval (pieceTot pa K0 c M a b) (t - (((a + b) / 2 : ℚ) : ℝ)) =
      eval M.p (t - c) + (midLower pa.q.P K0 pa.N a : ℝ) * ((t ^ 2 + 1 / 4) ^ 2) := by
    simp only [pieceTot, eval_padd, eval_psmul, eval_shiftPoly, eval_weightPoly]
    have e1 : ((((a + b) / 2 - c : ℚ)) : ℝ) + (t - (((a + b) / 2 : ℚ) : ℝ)) = t - c := by
      push_cast; ring
    rw [e1]; congr 2; ring
  have hM' : (M.e : ℝ) ≤ floorBound (pieceTot pa K0 c M a b) ((b - a) / 2) := by exact_mod_cast hM
  have hsym := symbol_lower105 pa.q.P K0 pa.N hKN a t (by exact_mod_cast ha0) hat
  have hW : (0 : ℝ) ≤ (t ^ 2 + 1 / 4) ^ 2 := by positivity
  have hWs := mul_le_mul_of_nonneg_left hsym hW
  have habs := (abs_le.mp hE).1
  unfold Fcert
  unfold wideFun at habs
  nlinarith

def checkChain (pa : Params) (K0 : ℕ) (c r : ℚ) (M : TM) (hi : ℚ) : ℚ → List ℚ → Bool
  | a, [] => decide (a = hi)
  | a, b :: rest => checkPiece pa K0 c r M a b && checkChain pa K0 c r M hi b rest

theorem checkChain_sound (pa : Params) (K0 : ℕ) (hats : Bool) (c r hi : ℚ) (hr : 0 ≤ r) :
    ∀ (l : List ℚ) (a : ℚ), checkChain pa K0 c r (wideTM pa K0 hats r c) hi a l = true →
      ∀ t : ℝ, (a : ℝ) < t → t ≤ hi → 0 ≤ Fcert t
  | [], a, h, t, hat, hth => by
    simp only [checkChain, decide_eq_true_eq] at h
    subst h; exact absurd hth (not_le.mpr hat)
  | b :: rest, a, h, t, hat, hth => by
    simp only [checkChain, Bool.and_eq_true] at h
    by_cases htb : t ≤ b
    · exact checkPiece_sound pa K0 hats c r a b hr h.1 t hat.le htb
    · exact checkChain_sound pa K0 hats c r hi hr rest b h.2 t (not_le.mp htb) hth

def cellCentre (lo hi : ℚ) : ℚ := if lo = 0 then 0 else (lo + hi) / 2
def cellRadius (lo hi : ℚ) : ℚ := if lo = 0 then hi else (hi - lo) / 2

def checkWide (pa : Params) (K0 : ℕ) (hats : Bool) (lo hi : ℚ) : List ℚ → Bool
  | [] => false
  | b :: rest =>
    decide (lo ≤ hi) &&
      checkPiece pa K0 (cellCentre lo hi) (cellRadius lo hi)
        (wideTM pa K0 hats (cellRadius lo hi) (cellCentre lo hi)) lo b &&
      checkChain pa K0 (cellCentre lo hi) (cellRadius lo hi)
        (wideTM pa K0 hats (cellRadius lo hi) (cellCentre lo hi)) hi b rest

theorem checkWide_sound (pa : Params) (K0 : ℕ) (hats : Bool) (lo hi : ℚ) (breaks : List ℚ)
    (h : checkWide pa K0 hats lo hi breaks = true) :
    ∀ t : ℝ, (lo : ℝ) ≤ t → t ≤ hi → 0 ≤ Fcert t := by
  cases breaks with
  | nil => simp [checkWide] at h
  | cons b rest =>
    simp only [checkWide, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlh, h1⟩, h2⟩ := h
    have hr : 0 ≤ cellRadius lo hi := by
      unfold cellRadius; split_ifs with h0
      · rw [h0] at hlh; exact hlh
      · linarith
    intro t hlo hhi
    by_cases htb : t ≤ b
    · exact checkPiece_sound pa K0 hats _ _ lo b hr h1 t hlo htb
    · exact checkChain_sound pa K0 hats _ _ hi hr rest b h2 t (not_le.mp htb) hhi

end AEGIS.RHKreinL105CheckerV1

#print axioms AEGIS.RHKreinL105CheckerV1.checkWide_sound

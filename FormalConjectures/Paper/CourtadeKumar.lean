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
# The Courtade–Kumar (most informative Boolean function) conjecture

Let `X` be uniform on the Boolean cube `{0,1}ⁿ` and let `Y` be the output of `n` independent binary
symmetric channels with crossover probability `p ∈ [0, 1]` on input `X` (each bit of `X` is flipped
independently with probability `p`). The **Courtade–Kumar conjecture** asserts that for every
Boolean function `f : {0,1}ⁿ → {0,1}`,

  `I(f(X); Y) ≤ 1 - h(p)`,

where `I` is mutual information and `h` is the binary entropy function, both in bits. The bound is
attained by the dictator functions `f(x) = xᵢ` (see `mutualInfo_dictator` below).

The formalisation below is elementary: all distributions are finite, the joint mass of `(f(X), Y)`
is written out explicitly, and mutual information is `H(f(X)) + H(Y) - H(f(X), Y)` with entropies in
bits computed from `Real.negMulLog`. Bits are `Bool`; the usual `{-1, 1}` or `{0, 1}` encodings of
the cube are equivalent.

*References:*
- [CK14] T. A. Courtade and G. R. Kumar, *Which Boolean functions maximize mutual information on
  noisy inputs?*, IEEE Trans. Inf. Theory 60 (2014), no. 8, 4515–4525.
- [CGJLMNW26] Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff,
  *A Proof of the Most Informative Boolean Function Conjecture*,
  [arXiv:2609.24931](https://arxiv.org/abs/2609.24931). A Lean 4 formalisation of the proof is at
  https://github.com/dpwoodru/general-courtade-kumar-lean.
-/

@[expose] public section

namespace CourtadeKumar

open scoped BigOperators

/-- The Boolean cube `{0,1}ⁿ`, with bits represented by `Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Binary entropy in bits, `h(p) = -p log₂ p - (1 - p) log₂ (1 - p)`, with `h(0) = h(1) = 0`. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Transition probability of `n` independent binary symmetric channels with crossover probability
`p`: `P(Y = y | X = x) = ∏ᵢ (if xᵢ = yᵢ then 1 - p else p)`. -/
noncomputable def bsc {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - p else p

/-- The joint probability `P(f(X) = b, Y = y)` for `X` uniform on the cube and `Y` the channel
output on input `X`. -/
noncomputable def jointProb {n : ℕ} (f : Cube n → Bool) (p : ℝ) (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then bsc p x y else 0

/-- Shannon entropy in bits of a probability mass function `q` on a finite type. -/
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (q a)) / Real.log 2

/-- The mutual information `I(f(X); Y) = H(f(X)) + H(Y) - H(f(X), Y)`, in bits. -/
noncomputable def mutualInfo {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointProb f p b y) + entropy (fun y => ∑ b, jointProb f p b y) -
    entropy (fun z : Bool × Cube n => jointProb f p z.1 z.2)

/-- **The Courtade–Kumar conjecture.** For every `n`, every Boolean function `f` on `{0,1}ⁿ` and
every crossover probability `p ∈ [0, 1]`, `I(f(X); Y) ≤ 1 - h(p)`. -/
@[category research solved, AMS 94,
  formal_proof using lean4 at "https://github.com/dpwoodru/general-courtade-kumar-lean/blob/c3599c05181ad357331b701edf8fd8ec75c88305/verification/comparator/CKChallenge/Solution.lean#L6"]
theorem courtade_kumar (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    mutualInfo f p ≤ 1 - binEntropyBits p := by
  sorry

/-! ## Tests of the definitions -/

@[category test, AMS 94]
theorem binEntropyBits_half : binEntropyBits (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa [binEntropyBits, one_div] using div_self h

@[category API, AMS 94]
private theorem sum_cube_one (F : Cube 1 → ℝ) :
    ∑ x, F x = F (fun _ => true) + F (fun _ => false) := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) F (fun b => F (fun _ => b))]
  · exact Fintype.sum_bool _
  · intro x
    simp only [Equiv.funUnique_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i default]

@[category API, AMS 94]
private theorem jointProb_dictator (p : ℝ) (b : Bool) (y : Cube 1) :
    jointProb (n := 1) (fun x => x 0) p b y = (if b = y 0 then 1 - p else p) / 2 := by
  unfold jointProb bsc
  rw [sum_cube_one]
  simp only [Fin.prod_univ_one]
  cases b <;> cases y 0 <;> simp <;> ring

@[category API, AMS 94]
private theorem negMulLog_div_two (x : ℝ) :
    Real.negMulLog (x / 2) = Real.negMulLog x / 2 + x * Real.log 2 / 2 := by
  rw [div_eq_mul_inv, Real.negMulLog_mul]
  have h : Real.negMulLog (2 : ℝ)⁻¹ = Real.log 2 / 2 := by
    simp only [Real.negMulLog, Real.log_inv]
    ring
  rw [h]
  ring

/-- The dictator `f(x) = x₀` attains the bound with equality, so the conjecture is sharp and the
statement is not vacuous. -/
@[category test, AMS 94]
theorem mutualInfo_dictator (p : ℝ) :
    mutualInfo (n := 1) (fun x => x 0) p = 1 - binEntropyBits p := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have jm : ∀ b y, jointProb (n := 1) (fun x => x 0) p b y =
      (if b = y 0 then 1 - p else p) / 2 := jointProb_dictator p
  have half : Real.negMulLog (1 / 2) = Real.log 2 / 2 := by
    rw [negMulLog_div_two, Real.negMulLog_one]
    ring
  have mf : ∀ b : Bool, ∑ y, jointProb (n := 1) (fun x => x 0) p b y = 1 / 2 := by
    intro b
    rw [sum_cube_one, jm, jm]
    cases b <;> simp <;> ring
  have my : ∀ y : Cube 1, ∑ b, jointProb (n := 1) (fun x => x 0) p b y = 1 / 2 := by
    intro y
    rw [Fintype.sum_bool, jm, jm]
    cases y 0 <;> simp <;> ring
  have e1 : entropy (fun b => ∑ y, jointProb (n := 1) (fun x => x 0) p b y) = 1 := by
    unfold entropy
    simp only [mf, Fintype.sum_bool, half]
    field_simp
    ring
  have e2 : entropy (fun y => ∑ b, jointProb (n := 1) (fun x => x 0) p b y) = 1 := by
    unfold entropy
    simp only [my]
    rw [sum_cube_one]
    simp only [half]
    field_simp
    ring
  have e3 : entropy (fun z : Bool × Cube 1 => jointProb (n := 1) (fun x => x 0) p z.1 z.2) =
      1 + binEntropyBits p := by
    unfold entropy binEntropyBits
    rw [Fintype.sum_prod_type, Fintype.sum_bool, sum_cube_one, sum_cube_one]
    simp only [jm]
    simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_div_two, negMulLog_div_two]
    field_simp
    ring
  unfold mutualInfo
  rw [e1, e2, e3]
  ring

end CourtadeKumar

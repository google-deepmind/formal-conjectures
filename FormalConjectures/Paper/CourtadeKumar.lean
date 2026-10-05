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

Let `X` be uniform on the Boolean cube `{0,1}ⁿ`. Independently of `X`, let the coordinates of `Z`
be i.i.d. Bernoulli random variables with parameter `p ∈ [0, 1]`, and put `Y = X xor Z`, so that
`Y` is the output of `n` independent binary symmetric channels with crossover probability `p` on
input `X`. The **Courtade–Kumar conjecture** asserts that for every Boolean function
`f : {0,1}ⁿ → {0,1}`,

  `I(f(X); Y) ≤ 1 - h(p)`,

where mutual information and binary entropy are measured in bits.

The usual restriction to `p ∈ [0, 1/2]` is equivalent to the range used here. For `p > 1/2`,
complementing every output bit replaces `Z` by its bitwise complement, which is i.i.d.
Bernoulli(`1 - p`) noise still independent of `X`; this bijective relabelling of the output
preserves `I(f(X); Y)`, and `h(1 - p) = h(p)`.

This file contains two formulations:

* `CourtadeKumar.courtade_kumar` is the elementary finite-sum statement used by the external
  Lean proof and its comparator check. Its definitions and statement are retained unchanged.
* `CourtadeKumar.variants.courtade_kumar_random_variable` is the random-variable formulation.
  Its product-law hypothesis specifies a uniform input and independent i.i.d. Bernoulli channel
  noise, and its conclusion is about the mutual information of the actual random variables.

`CourtadeKumar.courtade_kumar_iff_random_variable` proves that the two formulations are
equivalent, without using either research statement. Shannon entropy and mutual information of
finite-valued random variables are defined in
`FormalConjecturesForMathlib.InformationTheory.FiniteEntropy`.

For `n ≥ 1`, coordinate dictators attain the bound: `I(X_i; Y) = I(X_i; Y_i) = 1 - h(p)`, since
the other output coordinates are independent of `(X_i, Y_i)`. The test `mutualInfo_dictator`
checks `n = 1`.

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

open scoped BigOperators ENNReal
open MeasureTheory

/-! ## The elementary formulation

The probability interpretations of `bsc`, `jointProb` and `mutualInfo` assume `0 ≤ p ≤ 1`, and
`entropy q` is Shannon entropy when the masses `q` are nonnegative and sum to one; otherwise these
definitions are just total real-valued expressions. -/

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

/-! ## The random-variable formulation -/

/-- Coordinatewise xor on the Boolean cube. -/
def cubeXor {n : ℕ} (x z : Cube n) : Cube n :=
  fun i => Bool.xor (x i) (z i)

/-- The joint law of a uniform input and independent i.i.d. Bernoulli channel noise.

On this probability space the input and noise are the two coordinate projections. -/
noncomputable def inputNoiseLaw (n : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    Measure (Cube n × Cube n) :=
  (PMF.uniformOfFintype (Cube n)).toMeasure.prod
    (Measure.pi fun _ : Fin n =>
      ProbabilityTheory.bernoulliMeasure true false (⟨p, hp₀, hp₁⟩ : unitInterval))

@[category API, AMS 94]
instance (n : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (inputNoiseLaw n p hp₀ hp₁) := by
  unfold inputNoiseLaw
  infer_instance

namespace variants

/-- **The Courtade–Kumar conjecture, in random-variable form.**

The pushforward in the hypothesis is the joint distribution of `(X, Z)`. The uniform measure on
`Cube n` is the law of `n` i.i.d. Bernoulli(1/2) bits. The product law makes the coordinates of
`Z` i.i.d. Bernoulli(`p`) and makes the whole noise vector independent of `X`. In
`bernoulliMeasure true false p`, `true` has probability `p` and denotes a flip.

Conditional on `X`, `Y = X xor Z` flips each input coordinate independently with probability
`p`: this is the memoryless binary symmetric channel with crossover probability `p` from `X` to
`Y`. Every Boolean function is allowed, including constants. All maps between these finite
discrete types are measurable, so `f ∘ X` and `Y` are measurable. The conclusion is
`I(f(X); Y) ≤ 1 - h(p)` in bits, for the entire output vector `Y`.

The linked proof proves the elementary statement `CourtadeKumar.courtade_kumar`, and
`CourtadeKumar.courtade_kumar_iff_random_variable` transfers it to this formulation. -/
@[category research solved, AMS 94,
  formal_proof using lean4 at "https://github.com/dpwoodru/general-courtade-kumar-lean/blob/c3599c05181ad357331b701edf8fd8ec75c88305/verification/comparator/CKChallenge/Solution.lean#L6"]
theorem courtade_kumar_random_variable :
    ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
      (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Z : Ω → Cube n),
      Measurable X →
      Measurable Z →
      μ.map (fun ω => (X ω, Z ω)) =
        (PMF.uniformOfFintype (Cube n)).toMeasure.prod
          (Measure.pi fun _ : Fin n =>
            ProbabilityTheory.bernoulliMeasure true false
              (⟨p, hp₀, hp₁⟩ : unitInterval)) →
      let Y : Ω → Cube n := fun ω => cubeXor (X ω) (Z ω)
      InformationTheory.mutualInformationBits μ (f ∘ X) Y ≤ 1 - binEntropyBits p := by
  sorry

end variants

/-! ## API: equivalence of the formulations -/

@[category API, AMS 94]
private theorem cubeXor_eq_iff {n : ℕ} (x z y : Cube n) :
    cubeXor x z = y ↔ z = cubeXor x y := by
  simp only [funext_iff, cubeXor]
  exact forall_congr' fun i => by
    cases x i <;> cases z i <;> cases y i <;> decide

@[category API, AMS 94]
private theorem noiseProduct_cubeXor {n : ℕ} (p : ℝ) (x y : Cube n) :
    (∏ i, if cubeXor x y i then p else 1 - p) = bsc p x y := by
  unfold bsc
  apply Finset.prod_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

/-- The singleton masses of the input/noise product probability space. -/
@[category API, AMS 94]
private theorem inputNoiseLaw_real_singleton (n : ℕ) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (x z : Cube n) :
    (inputNoiseLaw n p hp₀ hp₁).real {(x, z)} =
      (2 : ℝ) ^ (-(n : ℤ)) * ∏ i, if z i then p else 1 - p := by
  have hB (b : Bool) :
      ((ProbabilityTheory.bernoulliMeasure true false
        (⟨p, hp₀, hp₁⟩ : unitInterval)) {b}).toReal = (if b then p else 1 - p) := by
    rw [← measureReal_def]
    cases b
    · rw [ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem _
        (measurableSet_singleton _) (by simp) (by simp)]
      simp
    · rw [ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem _
        (measurableSet_singleton _) (by simp) (by simp)]
      simp
  have hs : ({(x, z)} : Set (Cube n × Cube n)) =
      {x} ×ˢ Set.pi Set.univ (fun i => ({z i} : Set Bool)) := by
    ext w
    simp [Prod.ext_iff, Set.mem_pi, funext_iff]
  rw [measureReal_def, inputNoiseLaw, hs, Measure.prod_prod, Measure.pi_pi,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  simp [hB, Cube, zpow_neg]

/-- The joint probability of `(f(X), X xor Z)` on the product probability space is
the elementary `jointProb`. -/
@[category API, AMS 94]
private theorem inputNoiseLaw_jointProb (n : ℕ) (f : Cube n → Bool) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (b : Bool) (y : Cube n) :
    (inputNoiseLaw n p hp₀ hp₁).real
      ((fun ω : Cube n × Cube n => (f ω.1, cubeXor ω.1 ω.2)) ⁻¹' {(b, y)}) =
      jointProb f p b y := by
  classical
  have hsum (s : Set (Cube n × Cube n)) :
      (inputNoiseLaw n p hp₀ hp₁).real s =
        ∑ w, if w ∈ s then (inputNoiseLaw n p hp₀ hp₁).real {w} else 0 := by
    simpa [Finset.sum_filter] using
      (sum_measureReal_singleton (μ := inputNoiseLaw n p hp₀ hp₁)
        (Finset.univ.filter (fun w => w ∈ s))).symm
  rw [hsum]
  simp only [Fintype.sum_prod_type, Set.mem_preimage, Set.mem_singleton_iff,
    Prod.mk.injEq, inputNoiseLaw_real_singleton]
  unfold jointProb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = b
  · simp [h, cubeXor_eq_iff, noiseProduct_cubeXor]
  · simp [h]

/-- Mutual information on the explicit input/noise probability space equals the elementary
finite-sum expression. -/
@[category API, AMS 94]
theorem mutualInformationBits_model_eq (n : ℕ) (f : Cube n → Bool) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    InformationTheory.mutualInformationBits (inputNoiseLaw n p hp₀ hp₁)
      (fun ω : Cube n × Cube n => f ω.1) (fun ω => cubeXor ω.1 ω.2) =
      mutualInfo f p := by
  let μ := inputNoiseLaw n p hp₀ hp₁
  let T : Cube n × Cube n → Bool × Cube n := fun ω => (f ω.1, cubeXor ω.1 ω.2)
  have hT : Measurable T := measurable_of_countable T
  have hν (w : Bool × Cube n) : (μ.map T).real {w} = jointProb f p w.1 w.2 := by
    rw [measureReal_def, Measure.map_apply hT (measurableSet_singleton w)]
    exact inputNoiseLaw_jointProb n f p hp₀ hp₁ w.1 w.2
  have hMI : InformationTheory.mutualInformationBits (μ.map T) Prod.fst Prod.snd =
      InformationTheory.mutualInformationBits μ (fun ω => f ω.1) (fun ω => cubeXor ω.1 ω.2) :=
    InformationTheory.mutualInformationBits_map μ hT measurable_fst measurable_snd
  rw [← hMI, InformationTheory.mutualInformationBits_fst_snd]
  simp only [hν, mutualInfo, entropy]

/-- The same identity on any measurable space carrying the specified joint input/noise law. -/
@[category API, AMS 94]
theorem mutualInformationBits_of_inputNoiseLaw (n : ℕ) (f : Cube n → Bool) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Z : Ω → Cube n)
    (hX : Measurable X) (hZ : Measurable Z)
    (hlaw : μ.map (fun ω => (X ω, Z ω)) = inputNoiseLaw n p hp₀ hp₁) :
    InformationTheory.mutualInformationBits μ (f ∘ X) (fun ω => cubeXor (X ω) (Z ω)) =
      mutualInfo f p := by
  have hXZ : Measurable (fun ω => (X ω, Z ω)) := by fun_prop
  rw [← mutualInformationBits_model_eq n f p hp₀ hp₁, ← hlaw,
    InformationTheory.mutualInformationBits_map μ hXZ
      (measurable_of_countable (fun ω : Cube n × Cube n => f ω.1))
      (measurable_of_countable (fun ω : Cube n × Cube n => cubeXor ω.1 ω.2))]
  rfl

/-- The elementary formulation and the random-variable formulation are equivalent.

Neither direction uses either research declaration. -/
@[category API, AMS 94]
theorem courtade_kumar_iff_random_variable :
    type_of% @courtade_kumar ↔ type_of% @variants.courtade_kumar_random_variable := by
  constructor
  · intro h n f p hp₀ hp₁ Ω mΩ μ hμ X Z hX hZ hlaw
    change InformationTheory.mutualInformationBits μ (f ∘ X)
      (fun ω => cubeXor (X ω) (Z ω)) ≤ 1 - binEntropyBits p
    rw [mutualInformationBits_of_inputNoiseLaw n f p hp₀ hp₁ μ X Z hX hZ hlaw]
    exact h n f p hp₀ hp₁
  · intro h n f p hp₀ hp₁
    rw [← mutualInformationBits_model_eq n f p hp₀ hp₁]
    exact h n f p hp₀ hp₁ (Cube n × Cube n) (inputNoiseLaw n p hp₀ hp₁) Prod.fst Prod.snd
      measurable_fst measurable_snd (by
        change (inputNoiseLaw n p hp₀ hp₁).map id = inputNoiseLaw n p hp₀ hp₁
        simp)

/-- The random-variable formulation, stated over probability spaces in universe zero, implies
the same bound on probability spaces in any universe. This does not use either research
declaration. -/
@[category API, AMS 94]
theorem courtade_kumar_random_variable_bound
    (hCK : type_of% @variants.courtade_kumar_random_variable)
    (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Z : Ω → Cube n) (hX : Measurable X) (hZ : Measurable Z)
    (hlaw : μ.map (fun ω => (X ω, Z ω)) = inputNoiseLaw n p hp₀ hp₁) :
    let Y : Ω → Cube n := fun ω => cubeXor (X ω) (Z ω)
    InformationTheory.mutualInformationBits μ (f ∘ X) Y ≤ 1 - binEntropyBits p := by
  change InformationTheory.mutualInformationBits μ (f ∘ X)
    (fun ω => cubeXor (X ω) (Z ω)) ≤ 1 - binEntropyBits p
  rw [mutualInformationBits_of_inputNoiseLaw n f p hp₀ hp₁ μ X Z hX hZ hlaw]
  exact (courtade_kumar_iff_random_variable.mpr hCK) n f p hp₀ hp₁

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

/-- Algebraic identity for the one-coordinate dictator `f(x) = x₀`. For `p ∈ [0, 1]`, it shows
that the bound is attained, so the conjecture is sharp and the statement is not vacuous. -/
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

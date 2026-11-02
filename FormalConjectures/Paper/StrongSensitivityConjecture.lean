/-
Copyright 2025 The Formal Conjectures Authors.

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
# Strong Sensitivity Conjecture (`bs(f) ≤ s(f)^2`)

This file formalizes the *strong* sensitivity conjecture, asserting:

For every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`,
where bs(f) denotes block sensitivity and s(f) denotes sensitivity.

Huang's theorem proves a *quartic* upper bound, `bs(f) ≤ s(f)^4`, thereby
resolving the most widely known form of the sensitivity conjecture.

We now ask whether a stronger upper bound holds. Interestingly, the original
paper of Nisan and Szegedy, where the sensitivity conjecture first appeared,
already speculated that a *quadratic* upper bound might be the correct
relation. On the lower bound side, Rubinstein
(https://link.springer.com/article/10.1007/BF01200762) constructed Boolean functions
exhibiting the first quadratic separation. The best gap known before [OAI26],
due to Ambainis and Sun (https://arxiv.org/abs/1108.3494), was
`bs(f) ≥ (2/3)⋅s(f)^2`.

In September 2026 an internal OpenAI model disproved the quadratic bound [OAI26]: it
constructs total Boolean functions with `bs(f) / s(f)^2` arbitrarily large.

*References:*
* [OAI26] [A superquadratic separation between sensitivity and block sensitivity](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/paper.pdf)
  by OpenAI, OpenAI Math Release preprint (2026)
* [Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture](https://arxiv.org/abs/1907.00847)
  by Hao Huang (see Section 3, Concluding Remarks)
* [Variations on the Sensitivity Conjecture](https://arxiv.org/abs/1011.0354)
  by Pooya Hatami, Raghav Kulkarni, and Denis Pankratov (see Question 3.1)
* [On the Degree of Boolean Functions as Real Polynomials](https://link.springer.com/article/10.1007/BF01263419)
  by Noam Nisan, and Mario Szegedy (see Section 4, Open Problems)
-/

@[expose] public section

namespace StrongSensitivityConjecture

open Finset Function

section Sensitivity

variable {n : ℕ}

/-- Flip operator,
`flip x B` returns input `x` with bits in block `B` inverted. -/
def flip (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- Local sensitivity s(f,x),
number of indices where flipping one bit changes the value of `f`. -/
def sensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  #{i | f (flip x {i}) ≠ f x}

/-- Global sensitivity s(f),
maximum sensitivity of `f` over all inputs. -/
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (sensitivityAt f)

/-- Check validity of block collection (disjoint and sensitive),
A collection of blocks `cB` is valid for `f` at `x` if the blocks are
disjoint and flipping any block changes `f(x)`. -/
def IsValidBlockConfig (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (cB : Finset (Finset (Fin n))) : Prop :=
  (cB : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  ∀ B ∈ cB, f (flip x B) ≠ f x

/-- Local block sensitivity bs(f,x),
maximum size of a collection of sensitive, disjoint blocks for `f` at `x`. -/
noncomputable def blockSensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  open scoped Classical in
  Finset.sup {cB | IsValidBlockConfig f x cB} card

/-- Global block sensitivity of `f`,
maximum block sensitivity of `f` over all inputs. -/
noncomputable def blockSensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (blockSensitivityAt f)

set_option linter.style.formal_proof_palomar false in
/-- Strong Sensitivity Conjecture,
for every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`.

We call this the *strong* sensitivity conjecture because the original sensitivity
conjecture only asked for a polynomial bound in terms of `s(f)`. Huang's
celebrated result (often called the sensitivity theorem) gives a quartic bound,
`bs(f) ≤ s(f)^4`, thereby settling the original conjecture.

The quadratic bound is false. This was disproved by an internal OpenAI model in September 2026
[OAI26]; see the linked Lean proof. The linked statement, with its own definitions over an arbitrary
finite index type, is `strong_sensitivity_conjecture.variants.quantitative_separation`; see
`strong_sensitivity_conjecture_of_quantitative_separation`. -/
@[category research solved, AMS 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean#L12"]
theorem strong_sensitivity_conjecture :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), blockSensitivity f ≤ sensitivity f ^ 2 := by
  sorry


/-- Simple test example.
For multiples of four with $n \ge 12$, this Boolean function has block sensitivity
strictly greater than its sensitivity. Source:
[Nisan1989](https://dl.acm.org/doi/10.1145/73007.73038).

`nisanExample(x) = 1` iff the Hamming weight of $x$ is either
$n/2$ or $n/2 + 1$.
The function is symmetric, so its value only depends on the Hamming weight
of the input. -/
@[category test, AMS 68]
def nisanExample (n : ℕ) (x : Fin n → Bool) : Bool :=
  let w := #{i | x i}
  decide ((w : ℚ) ∈ ({(n / 2 : ℚ), (n / 2 : ℚ) + 1} : Finset ℚ))

/-- Assuming `n` is a positive multiple of 4, the sensitivity of `nisanExample`
is $n/2 + 2$. It is achieved by any $x$ with Hamming weight $n/2 + 2$: flipping
any of its $n/2 + 2$ one-bits moves the input into the accepting layer of weight $n/2 + 1$. -/
@[category test, AMS 68]
lemma nisanExample_sensitivity (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    sensitivity (nisanExample n) = n / 2 + 2 := by
  sorry

/-- Assuming `n` is a multiple of 4 and $n \ge 8$, the block sensitivity of
`nisanExample` is $3n/4$, achieved by any $x$ with Hamming weight $n/2$.
An optimal block configuration uses all $n/2$ one-bits as singleton blocks
and forms $n/4$ disjoint size-2 blocks from the zero-bits. -/
@[category test, AMS 68]
lemma nisanExample_blockSensitivity (n : ℕ) (hn : 4 ∣ n) (hn_large : 8 ≤ n) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  sorry

end Sensitivity

/- ## The separation of [OAI26]

The definitions in `Separation` are copied from the Lean statement linked at
`strong_sensitivity_conjecture`. They index bits by an arbitrary finite type, and a valid block
configuration must also consist of nonempty blocks. -/

namespace Separation

open Classical in
/-- Flip operator over a finite index type, as defined in [OAI26]. -/
noncomputable def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

open Classical in
/-- Local sensitivity, as defined in [OAI26]. -/
noncomputable def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

open Classical in
/-- Global sensitivity, as defined in [OAI26]. -/
noncomputable def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

open Classical in
/-- Local block sensitivity, as defined in [OAI26]. -/
noncomputable def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

open Classical in
/-- Global block sensitivity, as defined in [OAI26]. -/
noncomputable def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

/-- On `Fin n`, the flip of [OAI26] is `flip`; only the decidability instance differs. -/
@[category API, AMS 68]
lemma flip_eq {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) :
    flip x B = StrongSensitivityConjecture.flip x B := by
  funext i
  by_cases h : i ∈ B <;> simp [flip, StrongSensitivityConjecture.flip, h]

/-- On `Fin n`, the sensitivity of [OAI26] is `sensitivity`. -/
@[category API, AMS 68]
lemma sensitivity_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    sensitivity f = StrongSensitivityConjecture.sensitivity f := by
  unfold sensitivity StrongSensitivityConjecture.sensitivity
  refine Finset.sup_congr (by ext; simp) fun x _ => ?_
  unfold sensitivityAt StrongSensitivityConjecture.sensitivityAt
  congr 1
  ext i
  simp [flip_eq]

/-- On `Fin n`, the block sensitivity of [OAI26] is at most `blockSensitivity`: every block
configuration it counts is valid. -/
@[category API, AMS 68]
lemma blockSensitivity_le {n : ℕ} (f : (Fin n → Bool) → Bool) :
    blockSensitivity f ≤ StrongSensitivityConjecture.blockSensitivity f := by
  unfold blockSensitivity StrongSensitivityConjecture.blockSensitivity
  refine Finset.sup_le fun x _ => le_trans ?_
    (Finset.le_sup (f := StrongSensitivityConjecture.blockSensitivityAt f) (Finset.mem_univ x))
  unfold blockSensitivityAt StrongSensitivityConjecture.blockSensitivityAt
  refine Finset.sup_le fun blocks _ => ?_
  split_ifs with h
  · have hv : IsValidBlockConfig f x blocks := ⟨fun A hA B hB hAB => h.1 A hA B hB hAB,
      fun B hB => by rw [← flip_eq]; exact (h.2 B hB).2⟩
    exact Finset.le_sup (by classical exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)
  · exact Nat.zero_le _

end Separation

set_option linter.style.formal_proof_palomar false in
/-- For every `d ≥ 1` there is a Boolean function `f` with
`bs(f) / s(f)^2 ≥ 2^d / (4 (d + 2)^2)`, stated with the definitions in `Separation`.

This was proved by an internal OpenAI model in September 2026 [OAI26]; see the linked Lean
proof. -/
@[category research solved, AMS 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean#L12"]
theorem strong_sensitivity_conjecture.variants.quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (Separation.blockSensitivity f : ℝ) / (Separation.sensitivity f : ℝ) ^ 2 := by
  sorry

/-- The quantitative separation of [OAI26] disproves the strong sensitivity conjecture: at
`d = 10` the ratio `bs(f) / s(f)^2` exceeds `1`. -/
@[category test, AMS 68]
theorem strong_sensitivity_conjecture_of_quantitative_separation
    (h : type_of% @strong_sensitivity_conjecture.variants.quantitative_separation) :
    type_of% @strong_sensitivity_conjecture := by
  intro hall
  obtain ⟨n, f, -, -, -, hf⟩ := h 10 (by norm_num)
  have key : (Separation.blockSensitivity f : ℝ) ≤ (Separation.sensitivity f : ℝ) ^ 2 := by
    rw [Separation.sensitivity_eq]
    exact_mod_cast (Separation.blockSensitivity_le f).trans (hall n f)
  have hle : (Separation.blockSensitivity f : ℝ) / (Separation.sensitivity f : ℝ) ^ 2 ≤ 1 := by
    rcases eq_or_ne (Separation.sensitivity f) 0 with h0 | h0
    · simp [h0]
    · exact div_le_one_of_le₀ key (by positivity)
  norm_num at hf
  linarith

end StrongSensitivityConjecture

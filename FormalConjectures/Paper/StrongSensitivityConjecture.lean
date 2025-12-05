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

import FormalConjectures.Util.ProblemImports
namespace StrongSensitivityConjecture

/-!
# Strong Sensitivity Conjecture (`bs(f) ≤ s(f)^2`)
*References:*
* [Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture](https://arxiv.org/abs/1907.00847)
  by Hao Huang (see Section 3, Concluding Remarks)
* [Variations on the Sensitivity Conjecture](https://arxiv.org/abs/1011.0354)
  by Pooya Hatami, Raghav Kulkarni, and Denis Pankratov (see Question 3.1)
* [On the Degree of Boolean Functions as Real Polynomials](https://link.springer.com/article/10.1007/BF01263419)
  by Noam Nisan, and Mario Szegedy (see Section 4, Open Problems)

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
exhibiting the first quadratic separation. The best currently
known gap, due to Ambainis and Sun (https://arxiv.org/abs/1108.3494), is
`bs(f) ≥ (2/3)⋅s(f)^2`.
-/

open Finset Function Classical

section Sensitivity

variable {n : ℕ}

-- Flip operator
/-- `flip x B` returns input `x` with bits in block `B` inverted. -/
def flip (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !(x i) else x i

-- Local sensitivity s(f,x)
/-- number of indices where flipping one bit changes the value of f. -/
def sensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (univ.filter fun i => f (flip x {i}) ≠ f x).card

-- Global sensitivity s(f)
/-- maximum sensitivity over all inputs. -/
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (sensitivityAt f)

-- Check validity of block collection (disjoint and sensitive)
/-- A collection of blocks `cB` is valid for `f` at `x` if the blocks are 
disjoint and flipping any block changes `f(x)`. -/
def isValidBlockConfig (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) 
    (cB : Finset (Finset (Fin n))) : Prop :=
  (cB : Set (Finset (Fin n))).PairwiseDisjoint id ∧ 
  ∀ B ∈ cB, f (flip x B) ≠ f x

-- Local block sensitivity bs(f,x)
/-- maximum size of a valid block collection at x. -/
noncomputable def blockSensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (univ.filter (fun cB => isValidBlockConfig f x cB)).sup card

-- Global block sensitivity bs(f)
/-- maximum block sensitivity over all inputs. -/
noncomputable def blockSensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (blockSensitivityAt f)

/-- Strong Sensitivity Conjecture -/
@[category research open, AMS 68]
theorem strong_sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  blockSensitivity f ≤ (sensitivity f) ^ 2 := by
  sorry

end Sensitivity
end StrongSensitivityConjecture
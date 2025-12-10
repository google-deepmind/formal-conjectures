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
exhibiting the first quadratic separation. The best currently
known gap, due to Ambainis and Sun (https://arxiv.org/abs/1108.3494), is
`bs(f) ≥ (2/3)⋅s(f)^2`.

*References:*
* [Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture](https://arxiv.org/abs/1907.00847)
  by Hao Huang (see Section 3, Concluding Remarks)
* [Variations on the Sensitivity Conjecture](https://arxiv.org/abs/1011.0354)
  by Pooya Hatami, Raghav Kulkarni, and Denis Pankratov (see Question 3.1)
* [On the Degree of Boolean Functions as Real Polynomials](https://link.springer.com/article/10.1007/BF01263419)
  by Noam Nisan, and Mario Szegedy (see Section 4, Open Problems)
-/

namespace StrongSensitivityConjecture

open Finset Function Classical

section Sensitivity

variable {n : ℕ}

/-- Flip operator,
`flip x B` returns input `x` with bits in block `B` inverted. -/
def flip (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- Local sensitivity s(f,x),
number of indices where flipping one bit changes the value of `f`. -/
def sensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (univ.filter fun i => f (flip x {i}) ≠ f x).card

/-- Global sensitivity s(f),
maximum sensitivity of `f` over all inputs. -/
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (sensitivityAt f)

/-- Check validity of block collection (disjoint and sensitive),
A collection of blocks `cB` is valid for `f` at `x` if the blocks are
disjoint and flipping any block changes `f(x)`. -/
def isValidBlockConfig (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (cB : Finset (Finset (Fin n))) : Prop :=
  (cB : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  ∀ B ∈ cB, f (flip x B) ≠ f x

/-- Local block sensitivity bs(f,x),
maximum size of a collection of sensitive, disjoint blocks for `f` at `x`. -/
noncomputable def blockSensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (univ.filter (fun cB => isValidBlockConfig f x cB)).sup card

/-- Global block sensitivity of `f`,
maximum block sensitivity of `f` over all inputs. -/
noncomputable def blockSensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (blockSensitivityAt f)

/-- Strong Sensitivity Conjecture,
for every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`.

We call this the *strong* sensitivity conjecture because the original sensitivity
conjecture only asked for a polynomial bound in terms of `s(f)`. Huang's
celebrated result (often called the sensitivity theorem) gives a quartic bound,
`bs(f) ≤ s(f)^4`, thereby settling the original conjecture.
-/
@[category research open, AMS 68]
theorem strong_sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
    blockSensitivity f ≤ sensitivity f ^ 2 := by
  sorry


/-- Simple test example,
A Boolean function whose block sensitivity is strictly greater than
its sensitivity. Source: [Nisan1989](https://dl.acm.org/doi/10.1145/73007.73038).

`nisanExample(x) = 1` iff the Hamming weight of `x` is either
`n/2` or `n/2 + 1`. We assume `n` is a multiple of 4. By analyzing `x`
with Hamming weight `n/2` (the function is symmetric, so only the weight
matters), one can check that

* `s(f) = n/2`,
* `bs(f) = 3n/4`.

The value of `bs(f)` comes from using all `n/2` 1-bits as singleton blocks,
and pairing the `n/2` 0-bits into `n/4` disjoint size-2 blocks.
-/
@[category test]
def nisanExample (n : ℕ) (x : Fin n → Bool) : Bool :=
  let w := #{i | x i}
  decide (w ∈ ({n / 2, n / 2 + 1} : Finset ℕ))


end Sensitivity
end StrongSensitivityConjecture

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

import FormalConjecturesUtil

/-!
# Green's Open Problem 38

*References:*
- [100 open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.38)
- [La79] Lovász, László. "On the Shannon capacity of a graph."
  IEEE Transactions on Information theory 25.1 (1979): 1-7.
- [Po20] Polak, Sven. "New methods in coding theory: Error-correcting codes and the Shannon capacity."
  arXiv preprint arXiv:2005.02945 (2020).
- [IRCR26] Itty, Nathaniel and Rosin, Christopher D. and Carstensen, Chase and Reichman, Daniel.
  "Improved lower bounds for the Shannon capacity of odd cycles." arXiv:2607.21517 (2026).
- [Ga26] Gao, Yu. "A recursive construction improving the lower bound on the Shannon capacity of
  $C_7$." arXiv:2607.27869 (2026).
- [BPZ26] Buys, Pjotr and Polak, Sven and Zuiddam, Jeroen. "Lean-verified lower bounds for the
  Shannon capacity of odd cycles." arXiv:2607.29681 (2026). Lean formalisation:
  https://github.com/spectra-research/shannon-capacity-lean
-/

open Filter Set
open scoped Pointwise

namespace Green38


/-- $A - A$ intersects $\{-1, 0, 1\}^n$ only at $0$. -/
def IntersectsOnlyAtZero {n : ℕ} (A : Finset (𝔽₇ n)) : Prop :=
  ∀ a ∈ A - A, (∀ i, a i ∈ ({-1, 0, 1} : Finset (ZMod 7))) → a = 0

/-- The set of cardinalities of all subsets A where A - A intersects {-1, 0, 1}^n only at 0. -/
def ValidCardinalities (n : ℕ) : Set ℕ :=
  { (A.card) | (A : Finset (𝔽₇ n)) (_ : IntersectsOnlyAtZero A) }

/-- {0, 2, 4} is a valid independent set in C_7, giving cardinality 3. -/
@[category test, AMS 5]
theorem green_38.test_n1_lower :
    3 ∈ ValidCardinalities 1 := by
  refine ⟨{![0], ![2], ![4]}, ?_, by decide⟩
  intro a ha
  simp at ha ⊢
  -- a is a difference of elements from {0, 2, 4}, check all cases
  cases ha
  · norm_num [← List.ofFn_injective.eq_iff]
    decide
  · revert ‹_›
    use by decide+revert ∘ List.mem_cons.1


/--
The largest subset $A \subset \mathbb{F}_7^n$ for which $A - A$ intersects $\{-1, 0, 1\}^n$ only
at $0$.
-/
noncomputable def LargestAdmissibleCardinality : ℕ → ℝ := fun n ↦
  (sSup (ValidCardinalities n) : ℕ)

/-- The lower bound constant $C_1 \approx 3.2578$ from [Po20]. -/
noncomputable def C₁ : ℝ := (367 : ℝ) ^ (5⁻¹ : ℝ)

/-- The upper bound constant $C_2 \approx 3.3177$ from [La79]. -/
noncomputable def C₂ : ℝ := (7 * Real.cos (Real.pi / 7)) / (1 + Real.cos (Real.pi / 7))

/-- Can we improve the lower bound? The answer sequence must be eventually nonnegative, since
`=O` compares norms.

Yes. Itty, Rosin, Carstensen and Reichman [IRCR26] found a valid set of size $134753$ in
$\mathbb{F}_7^{10}$ (an independent set in the tenth strong power of $C_7$). Taking products
gives valid sets of size $134753^{\lfloor n/10 \rfloor}$ in $\mathbb{F}_7^n$, see
`green_38.variants.lower_itty_rosin_carstensen_reichman`, so the growth rate is at least
$134753^{1/10} > 3.258020 > C_1$ (note $134753 > 367^2 = 134689$). Gao [Ga26] and then Buys,
Polak and Zuiddam [BPZ26] improved the rate further, to $3.258789\ldots$ and $3.2588\ldots$
respectively; the latter is formalised in Lean. The exact growth rate remains open. -/
@[category research solved, AMS 5 11]
theorem green_38.lower :
    let ans := (answer(fun n : ℕ ↦ (134753 : ℝ) ^ (n / 10)) : ℕ → ℝ)
    (∀ᶠ n in atTop, 0 ≤ ans n) ∧ ans ≤ᶠ[atTop] LargestAdmissibleCardinality ∧
    ∃ c > C₁, (fun n ↦ c ^ n) =O[atTop] ans := by
  sorry

/-- Can we improve the best upper bound? The base `c` must be positive, since `=O` compares
norms. -/
@[category research open, AMS 5 11]
theorem green_38.upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    LargestAdmissibleCardinality ≤ᶠ[atTop] ans ∧
    ∃ c : ℝ, 0 < c ∧ c < C₂ ∧ ans =O[atTop] (fun n ↦ c ^ n) := by
  sorry

/--
The lower bound $(C_1 - o(1))^n \leqslant |A|$ where $C_1 = 367^{1/5} \approx 3.2578$, from a
valid set of size $367$ in $\mathbb{F}_7^5$ [Po20, Section 9.1]. This was the best known bound
when Green's list was written; it has since been improved, see `green_38.lower`. -/
@[category research solved, AMS 5 11]
theorem green_38.variants.best_lower :
    ∀ ε ∈ Set.Ioo (0 : ℝ) C₁, ∀ᶠ n in atTop, (C₁ - ε) ^ n ≤ LargestAdmissibleCardinality n := by
  sorry

/--
Itty, Rosin, Carstensen and Reichman [IRCR26] found a valid set of size $134753$ in
$\mathbb{F}_7^{10}$. Products of copies of it, padded with zero coordinates, give
$134753^{\lfloor n/10 \rfloor} \leqslant |A|$ in $\mathbb{F}_7^n$. -/
@[category research solved, AMS 5 11]
theorem green_38.variants.lower_itty_rosin_carstensen_reichman (n : ℕ) :
    (134753 : ℝ) ^ (n / 10) ≤ LargestAdmissibleCardinality n := by
  sorry

/-- The current best upper bound is $|A| \leqslant (C_2 + o(1))^n$ where
$C_2 = \frac{7 \cos(\pi/7)}{1 + \cos(\pi/7)} \approx 3.3177$ [La79, Corollary 5]. -/
@[category research solved, AMS 5 11]
theorem green_38.variants.best_upper :
    ∀ ε > 0, ∀ᶠ n in atTop, LargestAdmissibleCardinality n ≤ (C₂ + ε) ^ n := by
  sorry

/-- 0 is a valid cardinality, since the empty set vacuously satisfies the condition. -/
@[category test, AMS 5 11]
theorem green_38.test_zero_mem_validCardinalities {n : ℕ} :
    0 ∈ ValidCardinalities n := by
  use ∅
  simp [IntersectsOnlyAtZero]

/-- The set of valid cardinalities we take the supremum over is bounded above. -/
@[category test, AMS 5 11]
theorem green_38.test_bound_above {n : ℕ} :
    BddAbove (ValidCardinalities n) := by
  use 7 ^ n
  rintro _ ⟨A, _, rfl⟩
  calc A.card
    _ ≤ Fintype.card (𝔽₇ n) := A.card_le_univ
    _ = _ := by simp

end Green38

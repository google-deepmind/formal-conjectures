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

import FormalConjectures.Util.ProblemImports
import Mathlib.InformationTheory.Hamming

/-!
# Ben Green's Open Problem 40

*Reference:* [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)

Let $r$ be a fixed positive integer, and let $H(r)$ be the Hamming ball of radius $r$ in $\mathbb{F}_2^n$. Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and $|V_n| = (f(r) + o(1))\frac{2^n}{|H(r)|}$. Does $f(r) \to \infty$?
-/

open Filter Topology Fintype
open scoped Pointwise

namespace Green40

/-- The vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def isCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- There exists an infinite sequence of $n$'s together with subspaces $V_n \leq \mathbb{F}_2^n$
with $V_n + H(r) = \mathbb{F}_2^n$ and $|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$. -/
def sequence_exists (r : ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ n in atTop, ∃ V : Submodule (ZMod 2) (𝔽₂ n),
    isCoveringSubspace n r V ∧
    |(Nat.card V : ℝ) * (Nat.card (hammingBall n r) : ℝ) / (2 ^ n : ℝ) - c| < ε

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ := sInf {c : ℝ | sequence_exists r c}

/-- Does $f(r) \to \infty$? [Gr24]-/
@[category research open, AMS 5 94]
theorem green_40 : answer(sorry) ↔ Tendsto f atTop atTop := by
  sorry

/-- The only value known is $f(1) = 1$, which follows from the existence of the Hamming code [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.sanity_f_one : f 1 = 1 := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def isCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

def subset_sequence_exists (r : ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ n in atTop, ∃ V : Finset (𝔽₂ n),
    isCoveringFinset n r V ∧
    |(V.card : ℝ) * (Nat.card (hammingBall n r) : ℝ) / (2 ^ n : ℝ) - c| < ε

noncomputable def f_tilde (r : ℕ) : ℝ := sInf {c : ℝ | subset_sequence_exists r c}

/-- Does $\tilde{f}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop atTop := by
  sorry

/-- It is known that $\tilde{f}(2) = 1$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.variants.arbitrary_subsets_sanity_f_tilde_two : f_tilde 2 = 1 := by
  sorry

/-- We evidently have $\tilde{f}(r) \le f(r)$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant for all n
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def sequence_exists_all (r : ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∃ V : Submodule (ZMod 2) (𝔽₂ n),
    isCoveringSubspace n r V ∧
    (Nat.card V : ℝ) * (Nat.card (hammingBall n r) : ℝ) / (2 ^ n : ℝ) ≤ c + ε

noncomputable def f_all (r : ℕ) : ℝ := sInf {c : ℝ | sequence_exists_all r c}

/-- Does $f_{\text{all}}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.all_n : answer(sorry) ↔ Tendsto f_all atTop atTop := by
  sorry

end Green40

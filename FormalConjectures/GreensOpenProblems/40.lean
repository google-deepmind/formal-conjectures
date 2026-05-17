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

*References:*
- [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)
- [Da90] Davydov, Alexander Abramovich. "Construction of linear covering codes."
  Problemy Peredachi Informatsii 26.4 (1990): 38-55.
- [CHL97] Cohen, G., Honkala, I., Litsyn, S., & Lobstein, A. (1997). Covering codes (Vol. 54). Elsevier.
- [St94] R. Struik, Covering codes, PhD Thesis, Eindhoven University of Technology, the Netherlands, 106 pp, 1994.

-/

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40

/-- The vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- Does $f(r) \to \infty$? [Gr24]-/
@[category research open, AMS 5 94]
theorem green_40 : answer(sorry) ↔ Tendsto f atTop (𝓝 ⊤) := by
  sorry

/-- The only value known is $f(1) = 1$, which follows from the existence of the Hamming code [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.sanity_f_one : f 1 = 1 := by
  sorry

/-- $f(r) \le r^r / r! \sim e^r$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  sorry

/-- The possibility that f(r) = 1 for all r has not been ruled out [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_eq_one_for_all : answer(sorry) ↔ ∀ r, f r = 1 := by
  sorry

/-- It is not known whether f(2) = 1 [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_two_eq_one : answer(sorry) ↔ f 2 = 1 := by
  sorry

/-- The best-known upper bound for $f(2)$ is $1.4238$ [CHL97]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound_f_two : f 2 ≤ (1.4238 : ℝ≥0∞) := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def IsCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : IsCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop

/-- Does $\tilde{f}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop (𝓝 ⊤) := by
  sorry

/-- It is known that $\tilde{f}(2) = 1$ [St94]. -/
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

noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop

/-- Does $f_{\text{all}}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.all_n : answer(sorry) ↔ Tendsto f_all atTop atTop := by
  sorry

end Green40

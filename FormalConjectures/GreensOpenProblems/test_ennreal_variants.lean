import FormalConjectures.Util.ProblemImports
import Mathlib.InformationTheory.Hamming

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40

abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

def isCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : isCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def isCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : isCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop

@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop atTop := by
  sorry

@[category research solved, AMS 5 94]
theorem green_40.variants.arbitrary_subsets_sanity_f_tilde_two : f_tilde 2 = 1 := by
  sorry

@[category research solved, AMS 5 94]
theorem green_40.f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  sorry

noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop

@[category research open, AMS 5 94]
theorem green_40.variants.all_n : answer(sorry) ↔ Tendsto f_all atTop atTop := by
  sorry

end Green40

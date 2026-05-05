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

/-- $f(r) \le r^r / r!$ (which is $\sim e^r$) [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  sorry

end Green40

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos260

open Filter SummationFilter


/- limit of an/n -> infinity -/
def an_div_n_tendsto_infinity (an : ℕ → ℝ) : Prop :=
/- so the 'function' an/n tends to positive infinity -/
Tendsto (fun n => an n / (n : ℝ)) atTop atTop

/- this defines the infinite sum of the sequence an / (2 ^ (an))-/
noncomputable def sum_of_sequence (an : ℕ → ℝ) : ℝ :=
∑'[conditional ℕ] n, (an n / 2 ^ (an n))

/- check if a sum is rational -/
def sum_is_rational (a : ℕ → ℝ) : Prop := ∃ r : ℚ, (sum_of_sequence a) = (r : ℝ)

/- So a is a function that maps natural to reals this is a(0), a(1), ... a (n) -/
/- then a(n)/n tendsto positive infinity -/
theorem erdos_260 (a : ℕ → ℝ) (h : StrictMono a) (h2 : an_div_n_tendsto_infinity a) :
/- then the sum of a(n)/ 2^(a(n)) is not rational -/
¬ sum_is_rational a := by sorry


end Erdos260

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
# Sharp entropic Rogers–Shephard inequality

For iid log-concave random vectors on $\mathbb R^n$, $h(X-X')-h(X)\le n\log 2$.
This is the conjecture in [MT20, Conjecture 6.1], attributed there to Madiman and Kontoyiannis.

*References:*
- [MT20] J. Melbourne and T. Tkocz, *Reversals of Rényi Entropy Inequalities under
  Log-Concavity*, arXiv:2005.10930v1 (2020), Conjecture 6.1.
  [Conjecture 6.1](https://arxiv.org/html/2005.10930v1#S6)
- [Ki26] K. Kitamura, *Sharp entropic Rogers–Shephard inequality*, Lean 4 proof (2026).
  [Proof repository](https://github.com/KitaKen1/entropic-rogers-shephard/tree/c397fa6e591babb5a95d6ba55943baa21c5486c7)
-/

@[expose] public section

namespace EntropicRogersShephardFC

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A probability density with respect to Lebesgue measure. -/
def ProbabilityDensity (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ (∫ x, f x) = 1

/-- Multiplicative log-concavity, including zeros and the endpoint weights. -/
def LogConcave (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    Real.rpow (f x) a * Real.rpow (f y) b ≤ f (a • x + b • y)

/-- The entropic Rogers–Shephard conjecture [MT20, Conjecture 6.1],
including finiteness of both entropies. The answer is affirmative [Ki26]. -/
@[category research solved, AMS 52 60 94,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/entropic-rogers-shephard/blob/c397fa6e591babb5a95d6ba55943baa21c5486c7/lean/FCSolution.lean"]
theorem entropic_rogers_shephard {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (X Y : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hf : ProbabilityDensity n f) (hl : LogConcave n f)
    (hX : HasLaw X (volume.withDensity (fun x => ENNReal.ofReal (f x))) P)
    (hY : HasLaw Y (volume.withDensity (fun x => ENNReal.ofReal (f x))) P)
    (hXY : IndepFun X Y P) :
    let g : (Fin n → ℝ) → ℝ := fun s => ∫ x, f x * f (x - s)
    HasLaw (fun ω => X ω - Y ω) (volume.withDensity (fun s => ENNReal.ofReal (g s))) P ∧
      Integrable (fun x => Real.negMulLog (f x)) volume ∧
      Integrable (fun s => Real.negMulLog (g s)) volume ∧
      (∫ s, Real.negMulLog (g s)) - (∫ x, Real.negMulLog (f x)) ≤ (n : ℝ) * Real.log 2 := by
  sorry

end EntropicRogersShephardFC

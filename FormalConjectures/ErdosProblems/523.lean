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
# Erdős Problem 523

*References:*
- [erdosproblems.com/523](https://www.erdosproblems.com/523)
- [Ha73] Halász, G., _On a result of Salem and Zygmund concerning random polynomials_.
  Studia Sci. Math. Hungar. (1973), 369–377.
- The probability model and maximum follow the Apache 2.0 formalization at
  https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos523.lean
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Erdos523

/-- A fair sign, regarded as a real-valued random variable. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) ⟨(1 / 2 : ℝ), by norm_num⟩

instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The probability law of one infinite sequence of independent fair signs. -/
noncomputable def signMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

instance : IsProbabilityMeasure signMeasure := by
  unfold signMeasure
  infer_instance

/-- The random polynomial with coefficients indexed from `0` through `n`. -/
noncomputable def randomPolynomial (ω : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ k

/-- The maximum modulus on the complex unit circle. The range is nonempty and compact. -/
noncomputable def maximumModulus (ω : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup (range fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖)

/--
Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where
$\epsilon_k\in \{-1,1\}$ independently uniformly at random for $0\leq k\leq n$.
Does there exist some constant $C>0$ such that, almost surely,
$\max_{|z|=1}|\sum_{k\leq n}\epsilon_k(t)z^k|=(C+o(1))\sqrt{n\log n}$?

This was settled by Halász [Ha73], who proved this is true with $C=1$.
-/
@[category research solved, AMS 30 60]
theorem erdos_523 : answer(True) ↔ ∃ C : ℝ, 0 < C ∧
    ∀ᵐ ω ∂signMeasure, Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
      atTop (𝓝 C) := by
  sorry

/-- Halász [Ha73] proved that the almost-sure limit in Erdős Problem 523 is $1$. -/
@[category research solved, AMS 30 60]
theorem erdos_523.variants.constant_one :
    ∀ᵐ ω ∂signMeasure, Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
      atTop (𝓝 1) := by
  sorry

end Erdos523

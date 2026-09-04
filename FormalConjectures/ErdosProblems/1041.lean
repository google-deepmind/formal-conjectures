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

import FormalConjecturesUtil

/-!
# Erdős Problem 1041

*Reference:* [erdosproblems.com/1041](https://www.erdosproblems.com/1041)
-/

open Polynomial MeasureTheory ENNReal

namespace Erdos1041

variable (n : ℕ) (f : ℂ[X]) (hn : n ≥ 2) (hnum : f.natDegree = n)
variable (h_monic : f.Monic)
variable (h : f.rootSet ℂ ⊆ Metric.ball 0 1)
include hn hnum h h_monic

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its 1-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

open scoped Classical in
/--
**Erdős–Herzog–Piranian Component Lemma** (Metric Properties of Polynomials, 1958):
If $f$ is a monic degree $n$ polynomial with all roots in the unit disk,
then some connected component
of $\{z \mid |f(z)| < 1\}$ contains at least two roots with multiplicity.

See p. 139, above Problem 5:
[EHP58] Erdős, P. and Herzog, F. and Piranian, G., _Metric properties of polynomials_.
  J. Analyse Math. (1958), 125-148.
-/
@[category research solved, AMS 32]
theorem exists_connected_component_contains_two_roots :
    ∃ C, C ⊆ {z | ‖f.eval z‖ < 1} ∧ IsConnected C ∧
      2 ≤ (f.roots.filter (· ∈ C)).card := by
  sorry

/--
Let
$$ f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[x] $$
with $|z_i| < 1$ for all $i$.

Conjecture: Must there always exist a path of length less than 2 in
$$ \{ z \in \mathbb{C} \mid |f(z)| < 1 \} $$
which connects two of the roots of $f$?
-/
@[category research open, AMS 32]
theorem erdos_1041 :
    ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
      Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ length (Set.range γ) < 2 := by
  sorry
end Erdos1041

namespace Erdos1041

/--
Under an explicit margin, every root of a small constant perturbation of a
monic split polynomial stays inside the open unit disc.

This is a quantitative root-retention lemma for polynomials whose roots
already lie in a strictly smaller disc. It does not produce a short path
inside `{z | ‖f(z)‖ < 1}` and does not settle `erdos_1041`.
-/
@[category research solved, AMS 32, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/f88e8b686908010a43e9078dda49abbabcfc4079/adapters/FormalConjecturesVariants.lean#L178-L186"]
theorem erdos_1041.variants.perturbed_roots_in_unit_disk
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ) (hε : 0 < ε)
    (hmargin : ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1 := by
  sorry

end Erdos1041

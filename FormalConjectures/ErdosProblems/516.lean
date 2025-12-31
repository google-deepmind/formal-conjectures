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
# Erdős Problem 516
*Reference:*
 - [erdosproblems.com/516](https://www.erdosproblems.com/516)
 - [Fu63] Fuchs, W. H. J., Proof of a conjecture of G. Pólya concerning gap series. Illinois J.
    Math. (1963), 661--667.
 - [Ko65] Kövari, Thomas, A gap-theorem for entire functions of infinite order. Michigan Math. J.
    (1965), 133--140.
-/

open scoped Real Nat
open Set Filter

/-- An entire function `f` is said to be of finite order if there exist numbers c, a ≥ 0
such that for all `z`, `‖f z‖ ≤ c * rexp ‖z‖ ^ a`. -/
def ofFiniteOrder {E F: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E → F) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ 0, ∃ a ≥ 0, ∀ z, ‖f z‖ ≤ c * rexp ‖z‖ ^ a

namespace Erdos516

noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log / (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log

/-- Let `f = ∑ aₖzⁿₖ` be a entire function of finite order such that `nₖ / k → ∞`.
Then `limsup (fun r => ratio r f) atTop = 1`. This is proved in [Fu63]. -/
@[category research solved, AMS 30]
theorem erdos_516.limsup_ratio_eq_one_Fabry_ofFiniteOrder {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z))
    (hf : ofFiniteOrder f) :
    limsup (fun r => ratio r f) atTop = 1 := by
  sorry

/-- Let `f = ∑ aₖzⁿₖ` be a entire function such that `nₖ > k (log k) ^ (2 + c)`.
Then `limsup (fun r => ratio r f) atTop = 1`. This is proved in [Ko65]. -/
@[category research solved, AMS 30]
theorem erdos_516.limsup_ratio_eq_one {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : ∃ c > 0, ∀ k, n k >  k * (k.log) ^ (2 + c)) {a : ℕ → ℂ}
    (hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) :
    limsup (fun r => ratio r f) atTop = 1 := by
  sorry

/-- Is it true that for all entire functions `f = ∑ aₖzⁿₖ` such that `∑' 1 / nₖ < ∞`,
`limsup (fun r => ratio r f) atTop = 1`? -/
@[category research open, AMS 30]
theorem erdos_516.limsup_ratio_eq_one_Fejer {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFejerGaps n)
    {a : ℕ → ℂ} (hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (hf : ofFiniteOrder f) :
    limsup (fun r => ratio r f) atTop = 1 := by
  sorry

end Erdos516

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
/-!
# Bugeaud Collection of Conjectures and Open Questions: Spectrum of Sequence
*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Men73] Mendès France, Michel. "Les ensembles de Bésineau."
    Séminaire Delange-Pisot-Poitou 15.1 (1973): 1-6.
-/

namespace Bugeaud

/--
The spectrum of a sequence $(x_n)_{n \ge 1}$ of real numbers is the set of
irrational real numbers $\theta \in (0, 1)$ such that the sequence
$(x_n - n\theta)_{n \ge 1}$ is not uniformly distributed modulo one.
-/
def Spectrum (x : ℕ → ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo (0 : ℝ) 1 ∧ Irrational θ ∧
    ¬ IsEquidistributedModuloOne (fun n => x n - n * θ)}

/--
Problem 10.4. Let $\xi$ be a non-zero real number and $\alpha > 1$ be a real
number. The spectrum of the sequence $(\xi \alpha^n)_{n \ge 1}$ is at most
countable. Posed by Mendès France [Men73].
-/
@[category research open, AMS 11]
lemma spectrum_xi_alpha_pow_countable (ξ : ℝ) (hξ : ξ ≠ 0) (α : ℝ) (hα : 1 < α) :
    (Spectrum (fun n => ξ * α ^ n)).Countable := by
  sorry

end Bugeaud

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
# Erdős Problem 335

Characterise those $A, B \subseteq \mathbb{N}$ with positive natural density such that
$d(A + B) = d(A) + d(B)$. The conjecture is that such sets must arise from measurable subsets
of a compact abelian group via a group rotation with the corresponding measure additivity property.

*Reference:* [erdosproblems.com/335](https://www.erdosproblems.com/335)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Classical Filter MeasureTheory

namespace Erdos335

/--
Erdős Problem 335 [ErGr80, p.51]:

Let $d(A)$ denote the natural density of $A \subseteq \mathbb{N}$. Characterise those
$A, B \subseteq \mathbb{N}$ with positive density such that $d(A + B) = d(A) + d(B)$.

One way this can happen is if there exists $\theta > 0$ such that
$A = \{n > 0 : \mathrm{fract}(n\theta) \in X_A\}$ and
$B = \{n > 0 : \mathrm{fract}(n\theta) \in X_B\}$ where
$X_A, X_B \subseteq \mathbb{R}/\mathbb{Z}$ are measurable with
$\mu(X_A + X_B) = \mu(X_A) + \mu(X_B)$.

The conjecture asks whether all such $A$ and $B$ are generated in a similar way
(possibly using other compact abelian groups in place of $\mathbb{R}/\mathbb{Z}$).
We formalize one direction of the specific $\mathbb{R}/\mathbb{Z}$ version of the
conjectured characterisation: if $d(A+B) = d(A)+d(B)$ with positive densities, then
$A$ and $B$ arise from measurable subsets of $[0,1)$ via an irrational rotation, with
the corresponding measure additivity property. The reverse direction (that such
constructions yield additive density) is not formalized here.
-/
@[category research open, AMS 5 11]
theorem erdos_335 :
    ∀ (A B : Set ℕ) (dA dB : ℝ),
      A.HasDensity dA →
      B.HasDensity dB →
      0 < dA → 0 < dB →
      (Set.image2 (· + ·) A B).HasDensity (dA + dB) →
      ∃ (θ : ℝ) (X_A X_B : Set ℝ),
        Irrational θ ∧
        MeasurableSet X_A ∧ MeasurableSet X_B ∧
        X_A ⊆ Set.Ico 0 1 ∧ X_B ⊆ Set.Ico 0 1 ∧
        volume X_A = ENNReal.ofReal dA ∧
        volume X_B = ENNReal.ofReal dB ∧
        -- Sumset in ℝ/ℤ, identified with [0,1) via fractional parts
        volume (Set.image2 (fun a b => Int.fract (a + b)) X_A X_B) =
          volume X_A + volume X_B ∧
        (∀ n : ℕ, 0 < n → (n ∈ A ↔ Int.fract ((n : ℝ) * θ) ∈ X_A)) ∧
        (∀ n : ℕ, 0 < n → (n ∈ B ↔ Int.fract ((n : ℝ) * θ) ∈ X_B)) := by
  sorry

end Erdos335

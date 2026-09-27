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
# Erdős Problem 114

*References:*
- [erdosproblems.com/114](https://www.erdosproblems.com/114)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*. J.
  Analyse Math. (1958), 125-148.
- [ErHa99] Eremenko, Alexandre and Hayman, Walter, *On the length of lemniscates*. Michigan
  Math. J. (1999), 409-415.
- [FrNa09] Fryntov, Alexander and Nazarov, Fedor, *New estimates for the length of the
  Erdős-Herzog-Piranian lemniscate*. (2009), 49-60.
- [Ta25] Tao, T., *The maximal length of the Erdős-Herzog-Piranian lemniscate in high degree*.
  arXiv:2512.12455 (2025).
-/

@[expose] public section

open Polynomial MeasureTheory

namespace Erdos114

/-- The lemniscate $\{z \in \mathbb{C} : |p(z)| = 1\}$ of a complex polynomial $p$. -/
def lemniscate (p : ℂ[X]) : Set ℂ := {z : ℂ | ‖p.eval z‖ = 1}

/--
The length of the lemniscate of $p$, taken to be its $1$-dimensional Hausdorff measure (which
agrees with arc length for rectifiable curves).
-/
noncomputable def lemniscateLength (p : ℂ[X]) : ENNReal := μH[1] (lemniscate p)

/--
If $p(z) \in \mathbb{C}[z]$ is a monic polynomial of degree $n$, is the length of the curve
$\{z \in \mathbb{C} : |p(z)| = 1\}$ maximised when $p(z) = z^n - 1$?

A problem of Erdős, Herzog, and Piranian [EHP58]. We require $n \geq 1$: for $n = 0$ the only
monic polynomial is $1$, whose level set is all of $\mathbb{C}$, while $z^0 - 1 = 0$ has an empty
level set.

Eremenko and Hayman [ErHa99] proved the case $n = 2$, Fryntov and Nazarov [FrNa09] proved that
$z^n - 1$ is a local maximiser, and Tao [Ta25] proved the conjecture for all sufficiently
large $n$.
-/
@[category research open, AMS 30]
theorem erdos_114 : answer(sorry) ↔ ∀ n : ℕ, 1 ≤ n → ∀ p : ℂ[X], p.Monic → p.natDegree = n →
    lemniscateLength p ≤ lemniscateLength (X ^ n - 1) := by
  sorry

/--
Tao [Ta25] proved that $z^n - 1$ is the maximiser (unique up to rotation and translation) for
all sufficiently large $n$.
-/
@[category research solved, AMS 30]
theorem erdos_114.variants.large_n : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℂ[X], p.Monic →
    p.natDegree = n → lemniscateLength p ≤ lemniscateLength (X ^ n - 1) := by
  sorry

/-- Eremenko and Hayman [ErHa99] proved the case $n = 2$. -/
@[category research solved, AMS 30]
theorem erdos_114.variants.two (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = 2) :
    lemniscateLength p ≤ lemniscateLength (X ^ 2 - 1) := by
  sorry

/--
The case $n = 1$: a monic linear polynomial is $z + a$, so its lemniscate is a translate of the
lemniscate of $z - 1$, and translations preserve Hausdorff measure.
-/
@[category test, AMS 30]
theorem erdos_114.variants.one (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = 1) :
    lemniscateLength p ≤ lemniscateLength (X ^ 1 - 1) := by
  have hpe : p = X + C (p.coeff 0) := by
    have := hp.as_sum; rw [hdeg] at this; simpa [Finset.sum_range_one] using this
  have hset : lemniscate p =
      (IsometryEquiv.addRight (1 + p.coeff 0)) ⁻¹' lemniscate (X ^ 1 - 1) := by
    ext z; rw [hpe]; simp [lemniscate]; ring_nf
  rw [lemniscateLength, lemniscateLength, hset, IsometryEquiv.hausdorffMeasure_preimage]

end Erdos114

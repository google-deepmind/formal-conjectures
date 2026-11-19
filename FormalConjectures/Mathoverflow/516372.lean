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
# Mathoverflow 516372

*Reference:* [mathoverflow/516372](https://mathoverflow.net/questions/516372)
asked by user *Jarek Duda*

See also:
* Y. Baryshnikov, J. Duda, W. Szpankowski, *Types of Markov fields and tilings*,
  IEEE Trans. Inf. Theory 62 (2016), doi:10.1109/TIT.2016.2573834.
* J. Duda, *Crystals, quasicrystals and autocrystals*, version 13, Section 17,
  [zenodo/23624259](https://zenodo.org/records/23624259).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Mathoverflow516372

/-- Binary configurations on the square lattice $\mathbb{Z}^2$. -/
abbrev Config := ℤ × ℤ → Bool

/-- A $2 \times 2$ tile: a binary pattern on $\{0,1\}^2$. -/
abbrev Tile := Fin 2 × Fin 2 → Bool

/-- The shift of a configuration by $v \in \mathbb{Z}^2$. -/
def shift (v : ℤ × ℤ) (x : Config) : Config := fun z => x (z + v)

/-- The $2 \times 2$ tile seen by the configuration $x$ at the origin. -/
def window (x : Config) : Tile := fun p => x (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))

/-- The vector of $2 \times 2$ tile frequencies of a measure on configurations. -/
def marginal (μ : Measure Config) : Tile → ℝ := fun t => (μ {x | window x = t}).toReal

/-- The set $K \subseteq \mathbb{R}^{16}$ of $2 \times 2$ marginals of shift-invariant
Borel probability measures on $\{0,1\}^{\mathbb{Z}^2}$. -/
def marginalBody : Set (Tile → ℝ) :=
  {p | ∃ μ : Measure Config, IsProbabilityMeasure μ ∧
    (∀ v : ℤ × ℤ, MeasurePreserving (shift v) μ μ) ∧ marginal μ = p}

/-- A configuration is $n$-periodic if it is invariant under the shifts by $(n,0)$ and
$(0,n)$. Every configuration with a finite shift-orbit is $n$-periodic for some $n > 0$. -/
def IsPeriodic (n : ℕ) (x : Config) : Prop :=
  ∀ z : ℤ × ℤ, x (z + ((n : ℤ), 0)) = x z ∧ x (z + (0, (n : ℤ))) = x z

/-- The $2 \times 2$ tile frequencies of an $n$-periodic configuration, counted over one
$n \times n$ period. This is the marginal of the uniform measure on its shift-orbit. -/
def periodicMarginal (n : ℕ) (x : Config) : Tile → ℝ := fun t =>
  ((Finset.univ.filter fun ij : Fin n × Fin n =>
      window (shift (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) x) = t).card : ℝ) / (n : ℝ) ^ 2

/--
Let $K \subseteq \mathbb{R}^{16}$ be the set of $2 \times 2$ marginals (the frequencies of the
sixteen binary $2 \times 2$ tiles) of shift-invariant Borel probability measures on
$\{0,1\}^{\mathbb{Z}^2}$. $K$ is a compact convex set. Is every extreme point of $K$ the
marginal of a periodic configuration?

For every window inside a line and for every window of three sites the analogous answer is
yes; for the $3 \times 3$ square and for an eight-site window it is no.
-/
@[category research open, question, AMS 37 52]
theorem mathoverflow_516372 :
    ∀ p ∈ Set.extremePoints ℝ marginalBody,
      ∃ n : ℕ, 0 < n ∧ ∃ x : Config, IsPeriodic n x ∧ p = periodicMarginal n x := by
  sorry

/-- The all-white configuration is $1$-periodic. -/
@[category test, AMS 37]
theorem isPeriodic_const_false : IsPeriodic 1 (fun _ => false) := by
  simp [IsPeriodic]

/-- The all-white configuration sees only the all-white tile. -/
@[category test, AMS 37]
theorem periodicMarginal_const_false :
    periodicMarginal 1 (fun _ => false) (fun _ => false) = 1 := by
  simp [periodicMarginal, window, shift]

end Mathoverflow516372

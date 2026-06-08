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
# Furstenberg's `times p, times q` conjectures

*Reference:* [arxiv/2303.01089](https://arxiv.org/abs/2303.01089)
**Around Furstenberg's times $p$, times $q$ conjecture: times $p$-invariant measures
with some large Fourier coefficients**
by *Catalin Badea, Sophie Grivaux*
-/

noncomputable section

open scoped Topology
open Filter MeasureTheory UnitAddCircle

namespace Arxiv.id2303_01089

notation "𝕋" => UnitAddCircle

/--
Two integers $p, q \ge 2$ are multiplicatively independent if
$\log p / \log q$ is irrational.
-/
def MultiplicativelyIndependent (p q : ℕ) : Prop := Irrational (Real.log p / Real.log q)

/--
The map $T_n$ sends $x$ to $nx \bmod 1$ on the additive circle.
-/
def Tn (n : ℕ) (x : 𝕋) := n • x

@[category API, AMS 28]
lemma Tn_continuous (n : ℕ) : Continuous (Tn n) := continuous_nsmul n

/--
A set $F$ is $T_n$-invariant if $T_n(F) \subseteq F$.
-/
def IsTnInvariant (n : ℕ) (F : Set 𝕋) : Prop := Tn n '' F ⊆ F

/--
A set $A$ is an atom if it has positive measure and for all $B \subseteq A$ measurable,
either $\mu(B) = 0$ or $\mu(B) = \mu(A)$.
-/
def MeasureTheory.IsAtom {α : Type*} {m0 : MeasurableSpace α} (μ : Measure α) (A : Set α) : Prop :=
  0 < μ A ∧ ∀ B ⊆ A, MeasurableSet B → μ B = 0 ∨ μ B = μ A

/--
A measure is atomless if it has no atoms.
-/
class MeasureTheory.IsAtomLess {α : Type*} {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  NoAtoms : ∀ A, MeasurableSet A → ¬ MeasureTheory.IsAtom μ A

def UnitAddCircle.ProbabilityMeasure : ProbabilityMeasure 𝕋 :=
  ⟨volume, IsProbabilityMeasure.mk UnitAddCircle.measure_univ⟩

/--
**Conjecture 1.3** (the $\times p, \times q$ conjecture): the only atomless Borel probability
measure on $\mathbb{T}$ which is both $T_p$- and $T_q$-invariant is the Lebesgue measure.
-/
@[category research open, AMS 37]
theorem conjecture_1_3 {p q : ℕ} (hp : 2 <= p) (hq : 2 <= q) (hpq : MultiplicativelyIndependent p q)
    {μ : Measure 𝕋} [IsProbabilityMeasure μ] [MeasureTheory.IsAtomLess μ]
    (hmup : MeasurePreserving (Tn p) μ μ)
    (hmuq : MeasurePreserving (Tn q) μ μ) :
    μ = volume := by
  sorry

/--
**Conjecture 1.4**: if $\mu$ is an atomless $T_p$-invariant Borel probability measure on
$\mathbb{T}$, then $T_{q^n}\mu$ converges weak-star to Lebesgue measure.
This paper disproves the conjecture.
-/
@[category research solved, AMS 37]
theorem conjecture_1_4 :
    answer(False) ↔
      ∀ p q : ℕ, 2 <= p → 2 <= q → MultiplicativelyIndependent p q →
        ∀ μ : ProbabilityMeasure 𝕋,
          MeasureTheory.IsAtomLess μ.1 → MeasurePreserving (Tn p) μ μ →
          Tendsto (fun n : ℕ => μ.map (Tn_continuous (q ^ n)).aemeasurable) atTop
            (𝓝 UnitAddCircle.ProbabilityMeasure) := by
  sorry

end Arxiv.id2303_01089

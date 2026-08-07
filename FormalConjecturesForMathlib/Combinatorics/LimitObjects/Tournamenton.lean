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

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Combinatorics.Digraph.Basic
public import FormalConjecturesForMathlib.Combinatorics.LimitObjects.Graphon

@[expose] public section

open MeasureTheory MeasureTheory.Measure Finset

namespace LimitObjects

/--
A **tournamenton** is a measurable function `W : [0, 1] × [0, 1] → [0, 1]` satisfying the
tournament condition `W(x, y) + W(y, x) = 1`.
-/
structure Tournamenton where
  toFun : UnitInterval × UnitInterval → UnitInterval
  measurable : Measurable toFun
  tournament : ∀ x y : UnitInterval, (toFun (x, y) : ℝ) + (toFun (y, x) : ℝ) = 1

instance : CoeFun Tournamenton (fun _ => UnitInterval × UnitInterval → UnitInterval) := ⟨Tournamenton.toFun⟩

namespace Tournamenton

/-- Extensionality principle for `Tournamenton`. -/
@[ext]
theorem ext {W₁ W₂ : Tournamenton} (h : ∀ p, W₁ p = W₂ p) : W₁ = W₂ := by
  cases W₁; cases W₂; congr; funext p; exact h p

end Tournamenton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The directed edge finset of a finite digraph. -/
def digraphEdgeFinset (D : Digraph V) [DecidableRel D.Adj] : Finset (V × V) :=
  Finset.univ.filter (fun p => D.Adj p.1 p.2)

/--
The integrand for the homomorphism density $t_{\vec{T}}(W)$ of a digraph $D$
in a tournamenton $W$ given a configuration `x : V → [0, 1]`.
-/
def tournamentonHomIntegrand (D : Digraph V) [DecidableRel D.Adj]
    (W : Tournamenton) (x : V → UnitInterval) : ℝ :=
  ∏ p ∈ digraphEdgeFinset D, (W (x p.1, x p.2) : ℝ)

/--
The **homomorphism density** $t_{\vec{T}}(W)$ of a digraph $D$ in a tournamenton $W$
on $[0, 1]$ equipped with the Lebesgue measure `volume`.
-/
noncomputable def tournamentonHomDensity (D : Digraph V) [DecidableRel D.Adj]
    (W : Tournamenton) : ℝ :=
  ∫ x : V → UnitInterval, tournamentonHomIntegrand D W x ∂(Measure.pi fun _ => volume)

end LimitObjects

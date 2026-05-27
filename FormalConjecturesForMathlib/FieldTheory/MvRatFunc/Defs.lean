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

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-- The field of multivariate rational functions in variables indexed by `σ` over a commutative
ring `K`, defined as the fraction field of the multivariate polynomial ring `MvPolynomial σ K`. -/
abbrev MvRatFunc (σ K : Type*) [CommRing K] := FractionRing (MvPolynomial σ K)

/--
A rational function $g$ is defined at a point $x_0$ if $g$ can be written as $p / q$
where $p, q$ are polynomials and $q(x_0) \neq 0$.
-/
def IsDefined (σ K : Type*) [CommRing K] [IsDomain K] (g : MvRatFunc σ K) (x₀ : σ → K) : Prop :=
  ∃ p q : MvPolynomial σ K, g = (algebraMap _ _ p) / (algebraMap _ _ q) ∧ q.eval x₀ ≠ 0

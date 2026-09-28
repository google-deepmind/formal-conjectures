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

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Systems of parameters

For a local ring `R` of Krull dimension `d`, a *system of parameters* is a list of `d` elements
of `R` generating an ideal whose radical is the maximal ideal. Over a Noetherian local ring this
is the usual notion: a list of `d` elements of the maximal ideal with `R ⧸ Ideal.ofList rs`
Artinian. Krull's height theorem gives a system of parameters over every Noetherian local ring,
and that is the only case in which this definition is intended to be used.

## Main declarations

- `IsLocalRing.IsSystemOfParameters R rs`: the list `rs` is a system of parameters of `R`.
-/

@[expose] public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/--
A *system of parameters* of a local ring `R` is a list of `ringKrullDim R` elements of `R`
generating an ideal whose radical is the maximal ideal.
-/
structure IsSystemOfParameters (rs : List R) : Prop where
  /-- A system of parameters has `ringKrullDim R` elements. -/
  length_eq : (rs.length : WithBot ℕ∞) = ringKrullDim R
  /-- A system of parameters generates an ideal with radical the maximal ideal. -/
  radical_eq : (Ideal.ofList rs).radical = maximalIdeal R

variable {R}

/-- The elements of a system of parameters lie in the maximal ideal. -/
theorem IsSystemOfParameters.mem_maximalIdeal {rs : List R} (h : IsSystemOfParameters R rs)
    {r : R} (hr : r ∈ rs) : r ∈ maximalIdeal R :=
  h.radical_eq ▸ Ideal.le_radical (Ideal.subset_span hr)

variable (R)

/-- Over a local ring of Krull dimension zero, the empty list is a system of parameters. -/
theorem isSystemOfParameters_nil [Ring.KrullDimLE 0 R] :
    IsSystemOfParameters R ([] : List R) where
  length_eq := by
    simpa using ((ringKrullDimZero_iff_ringKrullDim_eq_zero (R := R)).mp ‹_›).symm
  radical_eq := by
    rw [Ideal.ofList_nil]
    exact Ring.KrullDimLE.nilradical_eq_maximalIdeal R

end IsLocalRing

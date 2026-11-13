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

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Product measurable spaces on matrices

Matrices carry the product measurable space of their entries. Countably indexed matrices over
a standard Borel space are standard Borel. The product measurable space agrees with the Borel
space of the product topology under the usual countability and second-countability assumptions.

These instances transfer Mathlib's corresponding facts for function spaces through the matrix
type synonym. `Matrix.measurable_iff` reduces matrix-valued measurability to its entries.

## References

* `Mathlib.MeasureTheory.Constructions.Polish.Basic`, countable products of standard Borel spaces.
* `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`, Borel structures on countable products.
-/

@[expose] public section

namespace Matrix

variable {m n R S : Type*}

/-- The product measurable space of all matrix entries. -/
instance [MeasurableSpace R] : MeasurableSpace (Matrix m n R) :=
  inferInstanceAs (MeasurableSpace (m → n → R))

/-- Countable matrices over a standard Borel space are standard Borel. -/
instance [Countable m] [Countable n] [MeasurableSpace R] [StandardBorelSpace R] :
    StandardBorelSpace (Matrix m n R) :=
  inferInstanceAs (StandardBorelSpace (m → n → R))

/-- For countable matrices over a second-countable Borel space, product and Borel spaces agree. -/
instance [Countable m] [Countable n] [MeasurableSpace R] [TopologicalSpace R]
    [SecondCountableTopology R] [BorelSpace R] : BorelSpace (Matrix m n R) :=
  inferInstanceAs (BorelSpace (m → n → R))

variable [MeasurableSpace R]

/-- Reading any entry of a matrix is measurable. -/
lemma measurable_entry (i : m) (j : n) :
    Measurable (fun A : Matrix m n R ↦ A i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- A matrix-valued map is measurable exactly when every entry is measurable. -/
lemma measurable_iff [MeasurableSpace S] {f : S → Matrix m n R} :
    Measurable f ↔ ∀ i j, Measurable (fun s ↦ f s i j) := by
  constructor
  · intro h i j
    exact (measurable_entry i j).comp h
  · intro h
    exact measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ h i j

/-- Transposition is measurable for the entrywise product measurable spaces. -/
@[fun_prop] lemma measurable_transpose :
    Measurable (transpose : Matrix m n R → Matrix n m R) :=
  measurable_iff.2 fun i j ↦ measurable_entry j i

end Matrix

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

public import FormalConjecturesForMathlib.Computability.WordRAM
public import FormalConjecturesForMathlib.Computability.BooleanSatisfiability

/-!
# Encoded inputs and parameters for fine-grained hypotheses

The number of represented variables is different from the encoded input length.
SAT time bounds allow a polynomial factor in the latter. Polynomial-time
hypotheses instead use the number of vectors, integers or vertices, with the
stated weight and shape promises.

References: Vassilevska Williams, *On some fine-grained questions in algorithms
and complexity*, §2.1 (SETH and integer 3SUM), §3 (OV), §6 (Exact k-Clique):
https://people.csail.mit.edu/virgi/eccentri.pdf.
Liu–Chen, STACS 2024, Conjecture 5 (randomized ETH):
https://doi.org/10.4230/LIPIcs.STACS.2024.49.
-/

@[expose] public section

namespace FineGrained

open Computability.BooleanSatisfiability

/-- Clause width restriction; polarity and repeated occurrences are retained. -/
def WidthAtMost (k : ℕ) (f : Formula) : Prop :=
  ∀ clause ∈ f, clause.length ≤ k

instance (k : ℕ) (f : Formula) : Decidable (WidthAtMost k f) := by
  unfold WidthAtMost
  infer_instance

/-- Number of distinct variables actually represented, not the largest variable name. -/
def variableCount (f : Formula) : ℕ := (support f).card

/-- Exact SAT truth value; the exhaustive definition does not claim a fast algorithm. -/
def sat (f : Formula) : Bool :=
  decide (SatisfiableWith (fun bs => bs.any id) f)

/-- A time bound 2^(a*n/b), with integer-floor rounding and a polynomial input factor. -/
def satTime (a b degree : ℕ) (f : Formula) : ℕ :=
  ((BitstringEncoding.bitEncode f).length + 1) ^ degree *
    2 ^ (a * variableCount f / b)

/-- A uniform bounded-error word-RAM solver at a specified exponential rate.
For encoded length L and time budget T, word width is O(log(max L T + 2)),
so the address space is not restricted to polynomial size in L. The program,
polynomial degree, word-size coefficient and time multiplier are fixed globally. -/
def HasSatTime (k a b : ℕ) : Prop :=
  0 < b ∧ ∃ degree : ℕ,
    WordRAM.HasTimeBudgetDecider (WidthAtMost k) sat (satTime a b degree)

@[simp]
theorem sat_eq_true (f : Formula) :
    sat f = true ↔ SatisfiableWith (fun bs => bs.any id) f := by simp [sat]

theorem threeSat_iff (f : Formula) : ThreeSat f ↔ WidthAtMost 3 f ∧ sat f = true := by
  simp [ThreeSat, WidthAtMost]

/-- Input dimension and two explicit lists of Boolean vectors. -/
abbrev OVInput := ℕ × (List (List Bool) × List (List Bool))

/-- Both sets have the same cardinality and every vector has the stated dimension. -/
def ValidOV (x : OVInput) : Prop :=
  x.2.1.Nodup ∧ x.2.2.Nodup ∧ x.2.1.length = x.2.2.length ∧
    (∀ v ∈ x.2.1, v.length = x.1) ∧ (∀ v ∈ x.2.2, v.length = x.1)

instance (x : OVInput) : Decidable (ValidOV x) := by
  unfold ValidOV
  infer_instance

/-- Integer dot product zero for Boolean vectors: no coordinate is one in both. -/
def Orthogonal (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ pair ∈ a.zip b, (pair.1 && pair.2) = false

instance (a b : List Bool) : Decidable (Orthogonal a b) := by
  unfold Orthogonal
  infer_instance

/-- At each common coordinate, at least one vector is zero. -/
theorem orthogonal_iff (a b : List Bool) :
    Orthogonal a b ↔ a.length = b.length ∧
      ∀ pair ∈ a.zip b, pair.1 = false ∨ pair.2 = false := by
  simp [Orthogonal]

def orthogonalVectors (x : OVInput) : Bool :=
  decide (∃ a ∈ x.2.1, ∃ b ∈ x.2.2, Orthogonal a b)

/-- Truly subquadratic in the number of vectors, with any fixed polynomial
factor in dimension. Numerator/denominator describe the exponent of n. -/
def HasOVTime (a b : ℕ) : Prop :=
  ∃ degree : ℕ, WordRAM.HasPowerTimeDecider ValidOV orthogonalVectors
    (fun x => x.2.1.length) (fun x => (x.1 + 1) ^ degree) a b

/-- Integer 3SUM uses a set of n integers in the source's interval [-n^4,n^4]. -/
def ValidThreeSum (xs : List ℤ) : Prop :=
  xs.Nodup ∧ ∀ z ∈ xs, z.natAbs ≤ xs.length ^ 4

instance (xs : List ℤ) : Decidable (ValidThreeSum xs) := by
  unfold ValidThreeSum
  infer_instance

/-- Three different entries sum to zero, as in Dudek–Gawrychowski–Starikovskaya,
arXiv:2001.01289v1, §1. On valid inputs their values are also distinct. -/
def ThreeSum (xs : List ℤ) : Prop :=
  ∃ i j k : Fin xs.length, i < j ∧ j < k ∧ xs[i] + xs[j] + xs[k] = 0

instance (xs : List ℤ) : Decidable (ThreeSum xs) := by
  unfold ThreeSum
  infer_instance

def threeSum (xs : List ℤ) : Bool := decide (ThreeSum xs)

/-- An explicit square array of edge-presence flags and signed integer weights. -/
abbrev WeightedGraph := List (List (Bool × ℤ))

/-- Total matrix access; graph validity prevents missing cells from being used. -/
def cell (g : WeightedGraph) (i j : ℕ) : Bool × ℤ :=
  ((g[i]?.getD [])[j]?).getD (false, 0)

/-- An undirected loopless graph with all stored weights in [-n^c,n^c].
The bound also applies to unused cells, preventing unbounded input padding. -/
def ValidWeightedGraph (c : ℕ) (g : WeightedGraph) : Prop :=
  (∀ row ∈ g, row.length = g.length) ∧
    (∀ i : Fin g.length, (cell g i i).1 = false) ∧
    (∀ i j : Fin g.length, cell g i j = cell g j i) ∧
    (∀ i j : Fin g.length, (cell g i j).2.natAbs ≤ g.length ^ c)

instance (c : ℕ) (g : WeightedGraph) : Decidable (ValidWeightedGraph c g) := by
  unfold ValidWeightedGraph
  infer_instance

/-- An exact-weight-zero triangle has three distinct vertices and three present edges. -/
def ExactTriangle (g : WeightedGraph) : Prop :=
  ∃ i j k : Fin g.length, i < j ∧ j < k ∧
    (cell g i j).1 = true ∧ (cell g j k).1 = true ∧ (cell g k i).1 = true ∧
    (cell g i j).2 + (cell g j k).2 + (cell g k i).2 = 0

instance (g : WeightedGraph) : Decidable (ExactTriangle g) := by
  unfold ExactTriangle
  infer_instance

def exactTriangle (g : WeightedGraph) : Bool := decide (ExactTriangle g)

/-- Three ordered distinct indices require at least three entries. -/
theorem three_le_of_threeSum {xs : List ℤ} (h : ThreeSum xs) : 3 ≤ xs.length := by
  obtain ⟨i, j, k, hij, hjk, _⟩ := h
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  simp only [Fin.lt_def] at hij hjk
  omega

theorem three_le_of_exactTriangle {g : WeightedGraph} (h : ExactTriangle g) :
    3 ≤ g.length := by
  obtain ⟨i, j, k, hij, hjk, _⟩ := h
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  simp only [Fin.lt_def] at hij hjk
  omega

end FineGrained

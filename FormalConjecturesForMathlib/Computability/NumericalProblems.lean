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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Perm

/-!
# Encoded numerical and weighted decision problems

These predicates implement Karp's job sequencing and signed-integer generalizations
of his 0–1 integer programming, knapsack (subset-sum equality), partition and
weighted max-cut problems. See *Reducibility among Combinatorial Problems* (1972),
Main Theorem items 2, 18–21 and Appendix I, pp. 94, 95, 97, 103,
https://doi.org/10.1007/978-1-4684-2001-2_9.

Lists preserve multiplicity and explicitly represent every variable, job, and vertex.
Integer data use the existing binary encoding. Matrices for integer programming are
column-major; cut matrices are symmetric with zero diagonal, and zero denotes a missing
or zero-weight edge. Malformed structured inputs are rejected.

Karp's Appendix I uses positive integers for subset sum, partition and edge weights,
and nonnegative components for the right-hand-side vector. Here these inputs may
also be signed. Job parameters retain the source's positivity requirements.

Decidability uses finite exhaustive enumeration. No polynomial-time algorithm is claimed.
-/

@[expose] public section

namespace Computability.NumericalProblems

/-- Sum of selected entries of an integer list; equal values at different indices remain
separate choices. -/
def selectedSum (values : List ℤ) (chosen : Finset (Fin values.length)) : ℤ :=
  ∑ i ∈ chosen, values[i]

@[simp]
theorem selectedSum_empty (values : List ℤ) : selectedSum values ∅ = 0 := by
  simp [selectedSum]

/-- Signed-integer generalization of Karp's positive-input KNAPSACK (subset-sum equality). -/
def SubsetSum (input : List ℤ × ℤ) : Prop :=
  ∃ chosen : Finset (Fin input.1.length), selectedSum input.1 chosen = input.2

instance (input : List ℤ × ℤ) : Decidable (SubsetSum input) := by
  unfold SubsetSum
  infer_instance

/-- Partition the indices into equal-sum parts, allowing signed entries beyond Karp's
positive-input convention. -/
def Partition (values : List ℤ) : Prop :=
  ∃ chosen : Finset (Fin values.length),
    selectedSum values chosen = selectedSum values chosenᶜ

instance (values : List ℤ) : Decidable (Partition values) := by
  unfold Partition
  infer_instance

/-- The two selected sums exhaust the list, including repeated values. -/
theorem selectedSum_add_compl (values : List ℤ) (chosen : Finset (Fin values.length)) :
    selectedSum values chosen + selectedSum values chosenᶜ =
      selectedSum values Finset.univ :=
  Finset.sum_add_sum_compl chosen (fun i ↦ values[i])

/-- Equal-sum partition is equivalently a subset whose doubled sum is the total. -/
theorem partition_iff (values : List ℤ) :
    Partition values ↔ ∃ chosen : Finset (Fin values.length),
      2 * selectedSum values chosen = selectedSum values Finset.univ := by
  constructor <;> rintro ⟨chosen, h⟩
  · exact ⟨chosen, by have := selectedSum_add_compl values chosen; omega⟩
  · exact ⟨chosen, by have := selectedSum_add_compl values chosen; omega⟩

/-- Explicit columns of an integer matrix, paired with its right-hand side.
The outer list represents all variables, including when there are no equations.
Column-major storage preserves that variable count without adding a separate
dimension field; equations are accessed across the columns.
The right-hand side may be signed, extending Karp's nonnegative-vector convention. -/
abbrev IntegerProgramInput := List (List ℤ) × List ℤ

/-- Every column has one entry for every right-hand-side component. -/
def ValidIntegerProgram (input : IntegerProgramInput) : Prop :=
  ∀ column ∈ input.1, column.length = input.2.length

instance (input : IntegerProgramInput) : Decidable (ValidIntegerProgram input) := by
  unfold ValidIntegerProgram
  infer_instance

/-- An entry of a column-major matrix; validity rules out the default case. -/
def coefficient (input : IntegerProgramInput) (i : Fin input.2.length)
    (j : Fin input.1.length) : ℤ :=
  (input.1[j][i.val]?).getD 0

/-- A 0–1 assignment selects columns whose sum is exactly the right-hand side. -/
def ZeroOneProgramming (input : IntegerProgramInput) : Prop :=
  ValidIntegerProgram input ∧ ∃ chosen : Finset (Fin input.1.length),
    ∀ i : Fin input.2.length, (∑ j ∈ chosen, coefficient input i j) = input.2[i]

instance (input : IntegerProgramInput) : Decidable (ZeroOneProgramming input) := by
  unfold ZeroOneProgramming
  infer_instance

/-- Selecting columns is equivalent to assigning one Boolean value to every variable. -/
theorem zeroOneProgramming_iff (input : IntegerProgramInput) :
    ZeroOneProgramming input ↔ ValidIntegerProgram input ∧
      ∃ x : Fin input.1.length → Bool, ∀ i : Fin input.2.length,
        (∑ j, if x j then coefficient input i j else 0) = input.2[i] := by
  constructor
  · rintro ⟨valid, chosen, h⟩
    refine ⟨valid, fun j ↦ decide (j ∈ chosen), fun i ↦ ?_⟩
    simpa [Finset.sum_ite] using h i
  · rintro ⟨valid, x, h⟩
    refine ⟨valid, Finset.univ.filter (fun j ↦ x j = true), fun i ↦ ?_⟩
    simpa [Finset.sum_filter] using h i

/-- Execution time, deadline, and penalty, in that order. -/
abbrev Job := ℕ × ℕ × ℕ

/-- The source requires all three job parameters to be positive. -/
def ValidJobs (jobs : List Job) : Prop :=
  ∀ job ∈ jobs, 0 < job.1 ∧ 0 < job.2.1 ∧ 0 < job.2.2

instance (jobs : List Job) : Decidable (ValidJobs jobs) := by
  unfold ValidJobs
  infer_instance

/-- Completion time at a position in a permutation, including the job at that position. -/
def completionTime (jobs : List Job) (order : Equiv.Perm (Fin jobs.length))
    (position : Fin jobs.length) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j ↦ j ≤ position), (jobs[order j]).1

/-- Total penalty of jobs completing strictly after their own deadlines.
A job completing exactly at its deadline incurs no penalty. -/
def latePenalty (jobs : List Job) (order : Equiv.Perm (Fin jobs.length)) : ℕ :=
  ∑ i, if (jobs[order i]).2.1 < completionTime jobs order i then (jobs[order i]).2.2 else 0

/-- A permutation has total late-job penalty at most the positive budget. -/
def JobSequencing (input : List Job × ℕ) : Prop :=
  ValidJobs input.1 ∧ 0 < input.2 ∧
    ∃ order : Equiv.Perm (Fin input.1.length), latePenalty input.1 order ≤ input.2

instance (input : List Job × ℕ) : Decidable (JobSequencing input) := by
  unfold JobSequencing
  infer_instance

/-- An explicitly represented weighted adjacency matrix. -/
abbrev WeightMatrix := List (List ℤ)

/-- Matrix entry; square validity rules out a missing column. -/
def weight (matrix : WeightMatrix) (i j : Fin matrix.length) : ℤ :=
  (matrix[i][j.val]?).getD 0

/-- Square, symmetric, zero-diagonal integer matrix of an undirected weighted graph. -/
def ValidWeightMatrix (matrix : WeightMatrix) : Prop :=
  (∀ row ∈ matrix, row.length = matrix.length) ∧
    (∀ i, weight matrix i i = 0) ∧ ∀ i j, weight matrix i j = weight matrix j i

instance (matrix : WeightMatrix) : Decidable (ValidWeightMatrix matrix) := by
  unfold ValidWeightMatrix
  infer_instance

/-- Sum of crossing weights, counting each edge once by orienting it out of the chosen side. -/
def cutWeight (matrix : WeightMatrix) (side : Finset (Fin matrix.length)) : ℤ :=
  ∑ i ∈ side, ∑ j ∈ sideᶜ, weight matrix i j

/-- Swapping the two sides does not change the weight of an undirected cut. -/
theorem cutWeight_compl {matrix : WeightMatrix} (h : ValidWeightMatrix matrix)
    (side : Finset (Fin matrix.length)) : cutWeight matrix sideᶜ = cutWeight matrix side := by
  simp only [cutWeight, compl_compl]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ h.2.2 j i

/-- There is a cut of weight at least the positive threshold. Negative edge weights are
allowed, extending Karp's positive-edge-weight convention. -/
def WeightedMaxCut (input : WeightMatrix × ℕ) : Prop :=
  ValidWeightMatrix input.1 ∧ 0 < input.2 ∧
    ∃ side : Finset (Fin input.1.length), (input.2 : ℤ) ≤ cutWeight input.1 side

instance (input : WeightMatrix × ℕ) : Decidable (WeightedMaxCut input) := by
  unfold WeightedMaxCut
  infer_instance

end Computability.NumericalProblems

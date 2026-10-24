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

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

variable {K : Type*} [Field K] [IsAlgClosed K] (a q : K)

open Polynomial in
/-- Over an algebraically closed field, every pair `(a, q)` is the sum and the product of some
pair of elements. -/
theorem exists_quadraticRoots : ∃ x : K × K, x.1 + x.2 = a ∧ x.1 * x.2 = q := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (C 1 * X ^ 2 + C (-a) * X + C q)
    (by rw [degree_quadratic (one_ne_zero : (1 : K) ≠ 0)]; norm_num)
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hα
  exact ⟨(α, a - α), by ring, by linear_combination -hα⟩

/-- A choice of pair of roots of `X ^ 2 - a * X + q`, that is, of elements with sum `a` and
product `q`. -/
noncomputable def quadraticRoots : K × K := (exists_quadraticRoots a q).choose

theorem quadraticRoots_add : (quadraticRoots a q).1 + (quadraticRoots a q).2 = a :=
  (exists_quadraticRoots a q).choose_spec.1

theorem quadraticRoots_mul : (quadraticRoots a q).1 * (quadraticRoots a q).2 = q :=
  (exists_quadraticRoots a q).choose_spec.2

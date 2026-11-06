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

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Irrationality sequences
-/

@[expose] public section

/-- A strictly increasing sequence $a_1 < a_2 < \cdots$ of positive integers is an irrationality
sequence if $\sum_n \frac{1}{t_n a_n}$ is irrational for every sequence of positive integers
$t_n$. -/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
    ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → Irrational (∑' n, 1 / ((t n : ℝ) * a n))

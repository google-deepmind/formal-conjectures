/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
def Y : ℕ → ℤ
  | 0 => -2
  | 1 => -56
  | n + 2 => -4 * Y (n + 1) - 64 * Y n

lemma Y_add_2 (n : ℕ) : Y (n + 2) = -4 * Y (n + 1) - 64 * Y n := rfl

lemma alg_id (A B : ℤ) :
  (-4 * (-4 * A - 64 * B) - 64 * A) ^ 2 =
  -48 * (-4 * A - 64 * B) ^ 2 + 3072 * A ^ 2 + 262144 * B ^ 2 := by ring

lemma Y_sq_rec (n : ℕ) : Y (n + 3) ^ 2 = -48 * Y (n + 2) ^ 2 + 3072 * Y (n + 1) ^ 2 + 262144 * Y n ^ 2 := by
  have h2 : Y (n + 2) = -4 * Y (n + 1) - 64 * Y n := Y_add_2 n
  have h3 : Y (n + 3) = -4 * Y (n + 2) - 64 * Y (n + 1) := Y_add_2 (n + 1)
  rw [h3, h2]
  exact alg_id (Y (n + 1)) (Y n)

lemma a_add_4 (k : ℕ) : a (k + 4) = -4 * a (k + 3) + 256 * a (k + 1) + 4096 * a k := rfl

lemma a_rec_zero (k : ℕ) : a (k + 4) + 4 * a (k + 3) - 256 * a (k + 1) - 4096 * a k = 0 := by
  have h := a_add_4 k
  linarith

lemma a_step_6 (k : ℕ) : a (k + 6) = -48 * a (k + 4) + 3072 * a (k + 2) + 262144 * a k := by
  have h1 := a_rec_zero (k + 2)
  have h2 := a_rec_zero (k + 1)
  have h3 := a_rec_zero k
  linarith

lemma a_step_odd (n : ℕ) : a (2 * n + 7) = -48 * a (2 * n + 5) + 3072 * a (2 * n + 3) + 262144 * a (2 * n + 1) := by
  have h := a_step_6 (2 * n + 1)
  have h1 : 2 * n + 1 + 6 = 2 * n + 7 := by omega
  have h2 : 2 * n + 1 + 4 = 2 * n + 5 := by omega
  have h3 : 2 * n + 1 + 2 = 2 * n + 3 := by omega
  rw [h1, h2, h3] at h
  exact h

lemma a_eq_Y_sq (n : ℕ) :
    a (2 * n + 1) = Y n ^ 2 ∧
    a (2 * n + 3) = Y (n + 1) ^ 2 ∧
    a (2 * n + 5) = Y (n + 2) ^ 2 := by
  induction n with
  | zero =>
    have h1 : a 1 = Y 0 ^ 2 := rfl
    have h2 : a 3 = Y 1 ^ 2 := rfl
    have h3 : a 5 = Y 2 ^ 2 := rfl
    exact ⟨h1, h2, h3⟩
  | succ n ih =>
    rcases ih with ⟨ih1, ih2, ih3⟩
    have h4 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    have h5 : 2 * (n + 1) + 3 = 2 * n + 5 := by omega
    have h6 : 2 * (n + 1) + 5 = 2 * n + 7 := by omega
    rw [h4, h5, h6]
    refine ⟨ih2, ih3, ?_⟩
    have ha := a_step_odd n
    have hy := Y_sq_rec n
    rw [ih1, ih2, ih3] at ha
    rw [ha]
    exact hy.symm
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  -- EVOLVE-BLOCK-START
  intro n
  have h := (a_eq_Y_sq n).1
  rw [h]
  exact ⟨Y n, by ring⟩
  -- EVOLVE-BLOCK-END

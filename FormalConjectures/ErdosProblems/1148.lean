/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1148

*Reference:* [erdosproblems.com/1148](https://www.erdosproblems.com/1148)
-/

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

set_option maxRecDepth 2000000

namespace Erdos1148

def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

def check_1148_y (x y : ℕ) : Bool :=
  let x2 := x * x
  let y2 := y * y
  if h : x2 + y2 < 6563 then true else
  let z2 := x2 + y2 - 6563
  if h2 : z2 > 6563 then true else
  let z := Nat.sqrt z2
  if h3 : z * z == z2 then false else true

def check_1148_x (x : ℕ) : Bool :=
  (List.range 82).all fun y => check_1148_y x y

def check_1148 : Bool :=
  (List.range 82).all check_1148_x

theorem check_1148_true : check_1148 = true := by
  native_decide

lemma check_x_true (x : ℕ) (hx : x < 82) : check_1148_x x = true := by
  have h := check_1148_true
  unfold check_1148 at h
  have h1 := List.all_eq_true.mp h x
  apply h1
  exact List.mem_range.mpr hx

lemma check_y_true (x y : ℕ) (hx : x < 82) (hy : y < 82) : check_1148_y x y = true := by
  have h := check_x_true x hx
  unfold check_1148_x at h
  have h1 := List.all_eq_true.mp h y
  apply h1
  exact List.mem_range.mpr hy

@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/YOUR_PR_NUMBER", AMS 11]
theorem erdos_1148.lower_bound : ¬ Erdos1148Prop 6563 := by
  intro h
  rcases h with ⟨x, y, z, h1, h2, h3, h4⟩
  have hx : x < 82 := by nlinarith [show x^2 ≤ 6563 from h2]
  have hy : y < 82 := by nlinarith [show y^2 ≤ 6563 from h3]
  have hz : z ^ 2 = x ^ 2 + y ^ 2 - 6563 := by omega
  have hz2 : z ^ 2 ≤ 6563 := h4
  
  have h_y_true := check_y_true x y hx hy
  
  unfold check_1148_y at h_y_true
  
  have h_not_lt : ¬(x * x + y * y < 6563) := by
    intro hlt
    have h_rw : x * x + y * y = x ^ 2 + y ^ 2 := by ring
    rw [h_rw] at hlt
    omega
    
  have h_not_gt : ¬(x * x + y * y - 6563 > 6563) := by
    intro hgt
    have h_rw : x * x + y * y = x ^ 2 + y ^ 2 := by ring
    rw [h_rw] at hgt
    omega
    
  have h_eq : Nat.sqrt (x * x + y * y - 6563) * Nat.sqrt (x * x + y * y - 6563) = x * x + y * y - 6563 := by
    have h_rw : x * x + y * y - 6563 = z * z := by
      have hrw1 : x * x = x ^ 2 := by ring
      have hrw2 : y * y = y ^ 2 := by ring
      have hrw3 : z * z = z ^ 2 := by ring
      rw [hrw1, hrw2, hrw3]
      omega
    rw [h_rw]
    rw [Nat.sqrt_eq]

  rw [dif_neg h_not_lt] at h_y_true
  rw [dif_neg h_not_gt] at h_y_true
  
  have h_beq : (Nat.sqrt (x * x + y * y - 6563) * Nat.sqrt (x * x + y * y - 6563) == x * x + y * y - 6563) = true := by
    exact beq_iff_eq.mpr h_eq
  
  rw [dif_pos h_beq] at h_y_true
  contradiction

end Erdos1148

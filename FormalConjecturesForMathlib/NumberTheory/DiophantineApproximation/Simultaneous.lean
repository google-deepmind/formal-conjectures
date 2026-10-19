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

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Simultaneous Dirichlet approximation

For finitely many reals $\theta_1, \dots, \theta_k$ and any $M \ge 1$ there is a positive integer
$q$ such that every $q \theta_i$ lies within $1/M$ of an integer. The proof is the usual
pigeonhole argument on the fractional parts of $q \theta_i$ for $0 \le q \le M^k$.
-/

@[expose] public section

namespace Real

/-- Simultaneous Dirichlet approximation: some positive `q` puts every `q * θ i` within `1 / M`
of an integer. -/
theorem exists_pos_forall_abs_mul_sub_int_lt (k M : ℕ) (hM : 0 < M) (θ : Fin k → ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ i, ∃ y : ℤ, |(q : ℝ) * θ i - y| < 1 / M := by
  let f : ℕ → (Fin k → ℕ) := fun q i => ⌊(M : ℝ) * Int.fract ((q : ℝ) * θ i)⌋₊
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmaps : ∀ q ∈ Finset.range (M ^ k + 1),
      f q ∈ Fintype.piFinset (fun _ : Fin k => Finset.range M) := by
    intro q _
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    apply (Nat.floor_lt (by positivity)).mpr
    have := Int.fract_lt_one ((q : ℝ) * θ i)
    nlinarith
  have hcard : (Fintype.piFinset (fun _ : Fin k => Finset.range M)).card <
      (Finset.range (M ^ k + 1)).card := by
    simp [Fintype.card_piFinset]
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ q : ℕ, 0 < q ∧ ∀ i, ∃ y : ℤ, |(q : ℝ) * θ i - y| < 1 / M := by
    intro a b hab hf
    refine ⟨b - a, by omega, fun i => ⟨⌊(b : ℝ) * θ i⌋ - ⌊(a : ℝ) * θ i⌋, ?_⟩⟩
    have hfi := congrFun hf i
    simp only [f] at hfi
    set u := (M : ℝ) * Int.fract ((a : ℝ) * θ i)
    set v := (M : ℝ) * Int.fract ((b : ℝ) * θ i)
    have hu0 : 0 ≤ u := by positivity
    have hv0 : 0 ≤ v := by positivity
    have h1 := Nat.floor_le hu0
    have h2 := Nat.lt_floor_add_one u
    have h3 := Nat.floor_le hv0
    have h4 := Nat.lt_floor_add_one v
    rw [hfi] at h1 h2
    have huv : |v - u| < 1 := by rw [abs_lt]; constructor <;> linarith
    have heq : ((b - a : ℕ) : ℝ) * θ i - ((⌊(b : ℝ) * θ i⌋ - ⌊(a : ℝ) * θ i⌋ : ℤ) : ℝ)
        = (v - u) / M := by
      simp only [u, v, Int.fract]
      rw [Nat.cast_sub hab.le]
      push_cast
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hMr]
    exact div_lt_div_of_pos_right huv hMr
  obtain ⟨a, _, b, _, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

end Real

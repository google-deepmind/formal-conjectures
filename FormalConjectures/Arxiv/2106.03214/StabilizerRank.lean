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

public import FormalConjecturesUtil

/-!
# Stabilizer rank of magic-state tensor powers

The stabilizer rank of a quantum state is the least number of stabilizer states whose complex
linear span contains it. On the Boolean cube, stabilizer states are quadratic phases supported
on affine subspaces. Tensor powers of the qubit $T$ magic state have amplitudes proportional
to $\exp(\pi i/4)^{|x|}$, where $|x|$ is Hamming weight. Their rank controls classical simulation
methods for circuits with non-Clifford gates.

*References:*
- S. Peleg, A. Shpilka and B. L. Volk,
  [Lower Bounds on Stabilizer Rank](https://arxiv.org/abs/2106.03214), Sections 1.4, 1.5 and 2.1.
- P. Sinha and B. Lovitz,
  [Improved bounds on stabilizer extent and Clifford rank](https://arxiv.org/abs/2610.06819).
-/

@[expose] public section

namespace Arxiv.«2106.03214».StabilizerRank

/-- The computational-basis indices of $n$ qubits. -/
abbrev BitVector (n : ℕ) := Fin n → ZMod 2

/-- A linear Boolean function with coefficient vector $l$. -/
def linearValue {n : ℕ} (l x : BitVector n) : ZMod 2 := ∑ i, l i * x i

/-- A Boolean quadratic function. Diagonal coefficients also supply linear terms. -/
def quadraticValue {n : ℕ} (q : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : BitVector n) : ZMod 2 := ∑ i, ∑ j, q i j * x i * x j

open scoped Classical in
/-- An unnormalized stabilizer function on the affine subspace $t+U$. -/
noncomputable def stabilizerFunction {n : ℕ} (U : Submodule (ZMod 2) (BitVector n))
    (t l : BitVector n) (q : Matrix (Fin n) (Fin n) (ZMod 2)) (x : BitVector n) : ℂ :=
  if x - t ∈ U then
    Complex.I ^ (linearValue l x).val * (-1) ^ (quadraticValue q x).val
  else 0

/-- An unnormalized quadratic-phase representative on a nonempty affine support.
Constant phases are absorbed by the coefficients in a decomposition. -/
def IsStabilizerFunction {n : ℕ} (f : BitVector n → ℂ) : Prop :=
  ∃ U t l q, f = stabilizerFunction U t l q

/-- An exact decomposition into $r$ stabilizer functions with arbitrary complex coefficients. -/
def HasStabilizerDecomposition {n : ℕ} (r : ℕ) (f : BitVector n → ℂ) : Prop :=
  ∃ (c : Fin r → ℂ) (s : Fin r → BitVector n → ℂ),
    (∀ j, IsStabilizerFunction (s j)) ∧ ∀ x, f x = ∑ j, c j * s j x

/-- The relative phase between the two amplitudes of the qubit $T$ state. -/
noncomputable def magicPhase : ℂ := Complex.exp (Real.pi * Complex.I / 4)

/-- Hamming weight of a Boolean vector. -/
def weight {n : ℕ} (x : BitVector n) : ℕ := ∑ i, (x i).val

/-- The amplitudes of $T^{\otimes n}$ with their common normalization removed. -/
noncomputable def magicState (n : ℕ) (x : BitVector n) : ℂ := magicPhase ^ weight x

@[category test, AMS 15 81]
theorem magic_state_zero (x : BitVector 0) : magicState 0 x = 1 := by
  simp [magicState, weight]

@[category test, AMS 15 81]
theorem magic_state_one_zero : magicState 1 (0 : BitVector 1) = 1 := by
  simp [magicState, weight]

@[category test, AMS 15 81]
theorem magic_state_one_one : magicState 1 (1 : BitVector 1) = magicPhase := by
  simp [magicState, weight, ZMod.val_one]

@[category test, AMS 15 81]
theorem magic_state_cons {n : ℕ} (b : ZMod 2) (x : BitVector n) :
    magicState (n + 1) (Fin.cons b x) = magicPhase ^ b.val * magicState n x := by
  simp [magicState, weight, Fin.sum_univ_succ, pow_add]

@[category test, AMS 15 81]
theorem magic_phase_fourth_power : magicPhase ^ 4 = -1 := by
  rw [magicPhase, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  ring

@[category test, AMS 15 81]
theorem stabilizer_function_fourth_power {n : ℕ}
    (U : Submodule (ZMod 2) (BitVector n)) (t l : BitVector n)
    (q : Matrix (Fin n) (Fin n) (ZMod 2)) (x : BitVector n) (hx : x - t ∈ U) :
    stabilizerFunction U t l q x ^ 4 = 1 := by
  classical
  simp only [stabilizerFunction, if_pos hx]
  have hi : (Complex.I ^ (linearValue l x).val) ^ 4 = 1 := by
    rw [← pow_mul, Nat.mul_comm (linearValue l x).val 4, pow_mul,
      Complex.I_pow_four, one_pow]
  have hneg : ((-1 : ℂ) ^ (quadraticValue q x).val) ^ 4 = 1 := by
    rw [← pow_mul, Nat.mul_comm (quadraticValue q x).val 4, pow_mul]
    norm_num
  rw [mul_pow, hi, hneg, one_mul]

@[category test, AMS 15 81]
theorem stabilizer_function_at_shift_ne_zero {n : ℕ}
    (U : Submodule (ZMod 2) (BitVector n)) (t l : BitVector n)
    (q : Matrix (Fin n) (Fin n) (ZMod 2)) : stabilizerFunction U t l q t ≠ 0 := by
  have h := stabilizer_function_fourth_power U t l q t (by simp)
  intro hz
  rw [hz] at h
  norm_num at h

@[category test, AMS 15 81]
theorem computational_basis_is_stabilizer {n : ℕ} (b : BitVector n) :
    IsStabilizerFunction (fun x => if x = b then (1 : ℂ) else 0) := by
  classical
  refine ⟨⊥, b, 0, 0, ?_⟩
  funext x
  simp [stabilizerFunction, linearValue, quadraticValue, sub_eq_zero]

@[category test, AMS 15 81]
theorem constant_one_is_stabilizer (n : ℕ) :
    IsStabilizerFunction (fun _ : BitVector n => (1 : ℂ)) := by
  refine ⟨⊤, 0, 0, 0, ?_⟩
  funext x
  simp [stabilizerFunction, linearValue, quadraticValue]

@[category test, AMS 15 81]
theorem magic_state_one_not_scalar_stabilizer :
    ¬ ∃ (c : ℂ) (s : BitVector 1 → ℂ),
      IsStabilizerFunction s ∧ ∀ x, magicState 1 x = c * s x := by
  classical
  rintro ⟨c, s, ⟨U, t, l, q, rfl⟩, h⟩
  have h0 := h (0 : BitVector 1)
  have h1 := h (1 : BitVector 1)
  rw [magic_state_one_zero] at h0
  rw [magic_state_one_one] at h1
  have hz : stabilizerFunction U t l q (0 : BitVector 1) ≠ 0 := by
    intro hs
    simp [hs] at h0
  have ho : stabilizerFunction U t l q (1 : BitVector 1) ≠ 0 := by
    intro hs
    have he : magicPhase ≠ 0 := Complex.exp_ne_zero _
    exact he (by simpa [hs] using h1)
  have hm0 : (0 : BitVector 1) - t ∈ U := by
    by_contra hm
    exact hz (by simp only [stabilizerFunction, if_neg hm])
  have hm1 : (1 : BitVector 1) - t ∈ U := by
    by_contra hm
    exact ho (by simp only [stabilizerFunction, if_neg hm])
  have hc : c ^ 4 = (1 : ℂ) := by
    calc
      c ^ 4 = c ^ 4 * stabilizerFunction U t l q (0 : BitVector 1) ^ 4 := by
        rw [stabilizer_function_fourth_power U t l q _ hm0, mul_one]
      _ = (c * stabilizerFunction U t l q (0 : BitVector 1)) ^ 4 := (mul_pow _ _ _).symm
      _ = 1 := by rw [← h0]; norm_num
  have hbad : (-1 : ℂ) = 1 := by
    calc
      -1 = magicPhase ^ 4 := magic_phase_fourth_power.symm
      _ = (c * stabilizerFunction U t l q (1 : BitVector 1)) ^ 4 := by rw [h1]
      _ = c ^ 4 * stabilizerFunction U t l q (1 : BitVector 1) ^ 4 := mul_pow _ _ _
      _ = 1 := by rw [hc, stabilizer_function_fourth_power U t l q _ hm1]; norm_num
  norm_num at hbad

/-- Every function has a finite decomposition using computational-basis stabilizer functions. -/
@[category API, AMS 15 81]
theorem exists_stabilizer_decomposition {n : ℕ} (f : BitVector n → ℂ) :
    ∃ r, HasStabilizerDecomposition r f := by
  classical
  let e := Fintype.equivFin (BitVector n)
  refine ⟨Fintype.card (BitVector n), (fun j => f (e.symm j)),
    (fun j x => if x = e.symm j then 1 else 0), ?_, ?_⟩
  · intro j
    exact computational_basis_is_stabilizer (e.symm j)
  · intro x
    simp only [mul_ite, mul_one, mul_zero, Equiv.eq_symm_apply]
    simp

/-- The nonzero magic-state function cannot be an empty sum. -/
@[category test, AMS 15 81]
theorem magic_state_not_empty_decomposition (n : ℕ) :
    ¬ HasStabilizerDecomposition 0 (magicState n) := by
  rintro ⟨c, s, _, h⟩
  have hzero := h (0 : BitVector n)
  simp [magicState, weight] at hzero

/--
Does the stabilizer rank of $T^{\otimes n}$ grow faster than every polynomial? This is the
super-polynomial lower-bound problem in [Peleg–Shpilka–Volk, Sections 1.1 and 1.5]. Its
normalization and its Clifford-equivalent $H$-state formulation have the same rank.
-/
@[category research open, question, AMS 15 81]
theorem superpolynomial_stabilizer_rank :
    ∀ d C : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℕ,
      HasStabilizerDecomposition r (magicState n) → C * n ^ d < r := by
  sorry

end Arxiv.«2106.03214».StabilizerRank

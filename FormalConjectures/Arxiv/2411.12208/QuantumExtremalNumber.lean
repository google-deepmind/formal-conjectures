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
# Quantum extremal numbers

*References:*
- [ZNSZ25] W. Zhang, Y. Ning, F. Shi and X. Zhang, *Extremal maximal entanglement*,
  Phys. Rev. A **111** (2025), 052410. [arXiv:2411.12208](https://arxiv.org/abs/2411.12208)
- [HS00] A. Higuchi and A. Sudbery, *How entangled can two couples get?*, Phys. Lett. A **273**
  (2000), 213–217. [arXiv:quant-ph/0005013](https://arxiv.org/abs/quant-ph/0005013)
- [HGS17] F. Huber, O. Gühne and J. Siewert, *Absolutely maximally entangled states of seven
  qubits do not exist*, Phys. Rev. Lett. **118** (2017), 200502.
  [arXiv:1608.06228](https://arxiv.org/abs/1608.06228)
- [Kit26] K. Kitamura, *A Lean proof that $\mathrm{Q}_{ex}(9) = 112$, with new bounds for 10 and
  11 qubits* (2026). [GitHub](https://github.com/KitaKen1/quantum-extremal-numbers-lean)
-/

@[expose] public section

open scoped BigOperators Matrix

namespace QuantumExtremalNumber

/-- The amplitudes of a state $\psi$ of `n` qubits, given in the computational basis
`Fin n → Fin 2`, as a matrix $M$: the rows are the configurations of the qubits in `A`, the
columns are the configurations of the other qubits. -/
noncomputable def amplitudeMatrix {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∉ A} → Fin 2) ℂ :=
  fun a b => ψ (fun i => if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, h⟩)

/-- The reduced density matrix $\rho_A = M M^*$ of $\psi$: the partial trace over the qubits
outside `A`. -/
noncomputable def reducedDensity {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∈ A} → Fin 2) ℂ :=
  amplitudeMatrix A ψ * (amplitudeMatrix A ψ)ᴴ

open scoped Classical in
/-- The number $m_k(\psi)$ of `k`-sets $A$ of qubits on which $\psi$ is maximally mixed,
$\rho_A = I / 2^k$. -/
noncomputable def numMaximallyMixed {n : ℕ} (k : ℕ) (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) : ℕ :=
  (Finset.univ.filter fun A : Finset (Fin n) =>
    A.card = k ∧ reducedDensity A ψ = ((2 : ℂ) ^ k)⁻¹ • 1).card

/-- The quantum extremal number $\mathrm{Q}_{ex}(n, k)$: the largest $m_k(\psi)$ over the
normalized states $\psi$ of `n` qubits. -/
noncomputable def Qex (n k : ℕ) : ℕ :=
  sSup {m | ∃ ψ : EuclideanSpace ℂ (Fin n → Fin 2), ‖ψ‖ = 1 ∧ numMaximallyMixed k ψ = m}

/-- Determine $\mathrm{Q}_{ex}(n, k)$ for all $n$ and $k$. -/
@[category research open, AMS 5 81]
theorem qex : Qex = answer(sorry) := by
  sorry

/-- $\mathrm{Q}_{ex}(4) = 4$ [HS00]. -/
@[category research solved, AMS 5 81]
theorem qex_four : Qex 4 2 = 4 := by
  sorry

/-- $\mathrm{Q}_{ex}(7) = 32$ [HGS17]. -/
@[category research solved, AMS 5 81]
theorem qex_seven : Qex 7 3 = 32 := by
  sorry

/-- $\mathrm{Q}_{ex}(8) = 56$ [ZNSZ25]. -/
@[category research solved, AMS 5 81]
theorem qex_eight : Qex 8 4 = 56 := by
  sorry

/-- $\mathrm{Q}_{ex}(9) = 112$. The lower bound is from [ZNSZ25] and the upper bound from
[Kit26]. -/
@[category research solved, AMS 5 81,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/quantum-extremal-numbers-lean/blob/7d7e3afdadabdb2fa964cea99711d05fc5652022/lean/Qex94/Main.lean#L75"]
theorem qex_nine : Qex 9 4 = answer(112) := by
  sorry

/-- Determine $\mathrm{Q}_{ex}(10)$. It is known that $200 \le \mathrm{Q}_{ex}(10)$ [ZNSZ25]
and $\mathrm{Q}_{ex}(10) \le 208$ [Kit26]. -/
@[category research open, AMS 5 81]
theorem qex_ten : Qex 10 5 = answer(sorry) := by
  sorry

/-- Determine $\mathrm{Q}_{ex}(11)$. It is known that $396 \le \mathrm{Q}_{ex}(11)$ [ZNSZ25]
and $\mathrm{Q}_{ex}(11) \le 422$ [Kit26]. -/
@[category research open, AMS 5 81]
theorem qex_eleven : Qex 11 5 = answer(sorry) := by
  sorry

/-- Determine $\mathrm{Q}_{ex}(12)$. It is known that
$540 \le \mathrm{Q}_{ex}(12) \le 792$ [ZNSZ25]. -/
@[category research open, AMS 5 81]
theorem qex_twelve : Qex 12 6 = answer(sorry) := by
  sorry

end QuantumExtremalNumber

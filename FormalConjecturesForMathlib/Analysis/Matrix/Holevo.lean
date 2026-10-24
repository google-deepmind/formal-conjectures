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

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Holevo information of finite-dimensional channels

This file defines von Neumann entropy, finite Kraus families, Holevo information,
and tensor products and independent uses of channels. Entropies use the natural logarithm.

Reference: K. Kitamura, *Strong Holevo additivity for qubit channels*, Lean 4 formalization
(2026), [statement definitions](https://github.com/KitaKen1/qubit-strong-additivity/blob/00e82103c022243203f9bfc2da428cc32eea3c78/lean/QubitAdditivity/Presentation/Model.lean).
-/

@[expose] public section

namespace QubitHolevo

noncomputable section
open scoped ComplexOrder Kronecker
open Matrix

/-- The von Neumann entropy $S(P) = -\operatorname{Tr}(P \log P)$, with the natural logarithm. -/
def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.negMulLog P).trace.re

/-- A finite family $(K_i)$ of matrices is a channel in Kraus form when
$\sum_i K_i^* K_i = 1$. -/
def IsKraus {ι κ ρ : Type*} [Fintype ι] [DecidableEq κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

/-- The Holevo information $\chi(\Phi)$ of the channel $\Phi(P) = \sum_i K_i P K_i^*$: the
supremum of $S(\Phi(\sum_a p_a \sigma_a)) - \sum_a p_a S(\Phi(\sigma_a))$ over all finite
ensembles of density matrices $\sigma_a$ with probabilities $p_a$. -/
def holevo {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : ℝ :=
  let Φ (P : Matrix κ κ ℂ) : Matrix ι ι ℂ := ∑ i, K i * P * (K i)ᴴ
  sSup {x | ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Matrix κ κ ℂ),
    (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ (∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1) ∧
    x = entropy (Φ (∑ a, p a • σ a)) - ∑ a, p a * entropy (Φ (σ a))}

/-- The Kraus family $(K_i \otimes L_j)$ of the tensor product of two channels. -/
def tensorKraus {ι κ ρ ι' κ' ρ' : Type*} (K : ρ → Matrix ι κ ℂ) (L : ρ' → Matrix ι' κ' ℂ) :
    ρ × ρ' → Matrix (ι × ι') (κ × κ') ℂ :=
  fun i ↦ K i.1 ⊗ₖ L i.2

/-- The Kraus family $(K_{i_1} \otimes \dots \otimes K_{i_n})$ of $n$ independent uses of a
channel. -/
def powerKraus {ι κ ρ : Type*} (K : ρ → Matrix ι κ ℂ) (n : ℕ) :
    (Fin n → ρ) → Matrix (Fin n → ι) (Fin n → κ) ℂ :=
  fun i a b ↦ ∏ k, K (i k) (a k) (b k)

end

end QubitHolevo

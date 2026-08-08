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

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv

public section

/-!
# The canonical Poisson bracket on a polynomial algebra in `2n` variables

For a commutative ring `R` and a finite type `σ`, we equip `MvPolynomial (σ ⊕ σ) R`
with its canonical Poisson bracket
$$\{f, g\} = \sum_{i} \left(\frac{\partial f}{\partial x_i}\frac{\partial g}{\partial y_i}
  - \frac{\partial f}{\partial y_i}\frac{\partial g}{\partial x_i}\right),$$
where $x_i$ (resp. $y_i$) denotes the variable indexed by `Sum.inl i` (resp. `Sum.inr i`).
This is the polynomial algebra underlying the `n`-th *canonical Poisson algebra* $P_n(R)$
when `σ = Fin n`.

Classical sources index the same object by `2n` variables $X_1, \dots, X_{2n}$ with bracket
$\{f, g\} = \sum_{i=1}^n (\partial f/\partial X_i \cdot \partial g/\partial X_{i+n}
- \partial f/\partial X_{i+n} \cdot \partial g/\partial X_i)$; here `Sum.inl i`
plays the role of $X_i$ and `Sum.inr i` the role of $X_{i+n}$
(see e.g. [AvdE07](https://arxiv.org/abs/math/0608009), Notations 1).
-/

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] [Fintype σ]

/-- The canonical Poisson bracket on `MvPolynomial (σ ⊕ σ) R`, given by
$\{f, g\} = \sum_{i} (\partial_{x_i} f \cdot \partial_{y_i} g
- \partial_{y_i} f \cdot \partial_{x_i} g)$ where $x_i$ (resp. $y_i$) is the variable
indexed by `Sum.inl i` (resp. `Sum.inr i`). -/
noncomputable def poissonBracket (f g : MvPolynomial (σ ⊕ σ) R) : MvPolynomial (σ ⊕ σ) R :=
  ∑ i : σ, (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g -
    pderiv (Sum.inr i) f * pderiv (Sum.inl i) g)

@[simp]
theorem poissonBracket_self (f : MvPolynomial (σ ⊕ σ) R) : poissonBracket f f = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [mul_comm, sub_self]

theorem poissonBracket_swap (f g : MvPolynomial (σ ⊕ σ) R) :
    poissonBracket f g = -poissonBracket g f := by
  rw [poissonBracket, poissonBracket, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem poissonBracket_X_inl_inl (i j : σ) :
    poissonBracket (X (Sum.inl i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inl j)) = 0 :=
  Finset.sum_eq_zero fun k _ => by
    rw [pderiv_X_of_ne (show (Sum.inl j : σ ⊕ σ) ≠ Sum.inr k from by simp),
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr k from by simp), mul_zero, zero_mul,
      sub_self]

@[simp]
theorem poissonBracket_X_inr_inr (i j : σ) :
    poissonBracket (X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inr j)) = 0 :=
  Finset.sum_eq_zero fun k _ => by
    rw [pderiv_X_of_ne (show (Sum.inr i : σ ⊕ σ) ≠ Sum.inl k from by simp),
      pderiv_X_of_ne (show (Sum.inr j : σ ⊕ σ) ≠ Sum.inl k from by simp), zero_mul, mul_zero,
      sub_self]

@[simp]
theorem poissonBracket_X_inl_inr [DecidableEq σ] (i j : σ) :
    poissonBracket (X (Sum.inl i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inr j)) =
      if i = j then 1 else 0 := by
  rw [poissonBracket, Finset.sum_eq_single i]
  · rw [pderiv_X_self, one_mul,
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr i from by simp), zero_mul, sub_zero]
    rcases eq_or_ne i j with rfl | h
    · simp
    · rw [pderiv_X_of_ne (show (Sum.inr j : σ ⊕ σ) ≠ Sum.inr i from by simpa using Ne.symm h),
        if_neg h]
  · intro k _ hk
    rw [pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inl k from by simpa using Ne.symm hk),
      pderiv_X_of_ne (show (Sum.inl i : σ ⊕ σ) ≠ Sum.inr k from by simp)]
    simp
  · simp

@[simp]
theorem poissonBracket_X_inr_inl [DecidableEq σ] (i j : σ) :
    poissonBracket (X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R) (X (Sum.inl j)) =
      if i = j then -1 else 0 := by
  rw [poissonBracket_swap, poissonBracket_X_inl_inr]
  split_ifs with h₁ h₂ h₂ <;> simp_all [Ne.symm]

end MvPolynomial

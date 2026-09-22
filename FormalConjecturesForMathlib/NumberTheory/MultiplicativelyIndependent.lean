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

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Multiplicatively independent integers

Two integers $p, q \ge 2$ are *multiplicatively independent* if $\log p / \log q$ is
irrational, equivalently if $p^m = q^n$ holds only for $m = n = 0$. The condition separates
bases whose expansions carry unrelated information, as in Cobham's theorem and in
Furstenberg's $\times p$, $\times q$ problems.

For a family of more than two integers the notion is the joint one: no nonzero integer tuple
`n` satisfies `∏ i, b i ^ n i = 1`. That is strictly stronger than pairwise independence, and
is what results such as Adamczewski–Faverjon's Mahler-method theorems assume.

## Main definitions

* `Nat.MultiplicativelyIndependent`: the relation for a pair of integers.
* `Nat.MultiplicativelyIndependentFamily`: the joint relation for a family of integers.
-/

namespace Nat

/--
Two integers $p, q \ge 2$ are *multiplicatively independent* if $\log p / \log q$ is
irrational, equivalently if $p^m = q^n$ holds only for $m = n = 0$.
-/
def MultiplicativelyIndependent (p q : ℕ) : Prop := Irrational (Real.log p / Real.log q)

/-- Multiplicative independence is symmetric. -/
theorem MultiplicativelyIndependent.symm {p q : ℕ} (h : MultiplicativelyIndependent p q) :
    MultiplicativelyIndependent q p := by
  rw [MultiplicativelyIndependent, ← inv_div]
  exact Irrational.inv h

/--
A family of integers is *multiplicatively independent* if there is no nonzero tuple of
integers $(n_i)$ with $\prod_i b_i^{n_i} = 1$; equivalently, the numbers $\log b_i$ are
linearly independent over $\mathbb{Q}$, which is the form used here.

This is the joint notion, which is strictly stronger than pairwise multiplicative
independence of the `b i` (`Nat.MultiplicativelyIndependentFamily.pairwise`). For a family of
two it agrees with `Nat.MultiplicativelyIndependent`, by `Nat.MultiplicativelyIndependent.family`.
-/
def MultiplicativelyIndependentFamily {ι : Type*} (b : ι → ℕ) : Prop :=
  LinearIndependent ℚ fun i => Real.log (b i)

/-- A multiplicatively independent family is pairwise multiplicatively independent. -/
theorem MultiplicativelyIndependentFamily.pairwise {ι : Type*} {b : ι → ℕ}
    (h : MultiplicativelyIndependentFamily b) :
    Pairwise fun i j => MultiplicativelyIndependent (b i) (b j) := by
  intro i j hij ⟨q, hq⟩
  have hj := h.ne_zero j
  refine (linearIndepOn_pair_iff _ hij.symm hj).1 (h.linearIndepOn _) q ?_
  rw [Rat.smul_def, hq, div_mul_cancel₀ _ hj]

/-- A multiplicatively independent pair is a multiplicatively independent family. -/
theorem MultiplicativelyIndependent.family {p q : ℕ} (h : MultiplicativelyIndependent p q) :
    MultiplicativelyIndependentFamily ![p, q] := by
  have hq : Real.log q ≠ 0 := by
    rintro hq
    rw [MultiplicativelyIndependent, hq, div_zero] at h
    exact h ⟨0, by norm_num⟩
  rw [MultiplicativelyIndependentFamily, linearIndependent_fin2]
  refine ⟨by simpa using hq, fun a ha => h ⟨a, ?_⟩⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  rw [← ha, Rat.smul_def, mul_div_assoc, div_self hq, mul_one]

end Nat

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

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.SumsOfSquares

@[expose] public section

/-!
# Pythagoras numbers

The *Pythagoras number* $p(R)$ of $R$ is the least $p$ such that every sum of squares in $R$ is a
sum of $p$ squares; see [Pfister1995] for fields and [CDLR1982] for rings. This file defines:

* `IsSumSqOfLength n a`: `a` is a sum of `n` squares, a counted refinement of Mathlib's `IsSumSq`;
* `pythagorasBounds R`: the set of `p` such that every sum of squares in `R` is a sum of `p`
  squares.

The Pythagoras number of `R` is `p` exactly when `IsLeast (pythagorasBounds R) p`. The set
`pythagorasBounds R` can be empty, in which case the Pythagoras number is infinite; by [CDLR1982]
this happens for $\mathbb{R}[X, Y]$. No numeric invariant is defined here, so that no convention
for the infinite case is needed.

The definitions and the correspondence with `IsSumSq` need only `[AddCommMonoid R] [Mul R]`; the
`AddCommMonoid` is what the sum `∑ i : Fin n` requires, since `IsSumSq` itself assumes only
`[Mul R] [Add R] [Zero R]`. Padding a sum of squares with zeros needs `0 * 0 = 0`, so
`IsSumSqOfLength.of_le` and `mem_pythagorasBounds_of_le` are stated for a
`NonUnitalNonAssocSemiring`.

## References

* [CDLR1982] M. D. Choi, Z. D. Dai, T. Y. Lam, B. Reznick, *The Pythagoras number of some
  affine algebras and local algebras*, J. reine angew. Math. 336 (1982), 45–82.
* [Pfister1995] A. Pfister, *Quadratic forms with applications to algebraic geometry and
  topology*, London Math. Soc. Lecture Note Ser. 217, Cambridge University Press, 1995.
-/

variable {R : Type*}

section AddCommMonoid

variable [AddCommMonoid R] [Mul R]

/-- `IsSumSqOfLength n a` means that `a` is a sum of `n` squares. -/
def IsSumSqOfLength (n : ℕ) (a : R) : Prop :=
  ∃ f : Fin n → R, a = ∑ i, f i * f i

variable (R) in
/-- The set of `p` such that every sum of squares in `R` is a sum of `p` squares. Its least
element, when it exists, is the Pythagoras number of `R`. -/
def pythagorasBounds : Set ℕ :=
  {p | ∀ a : R, IsSumSq a → IsSumSqOfLength p a}

theorem IsSumSqOfLength.isSumSq {n : ℕ} {a : R} (h : IsSumSqOfLength n a) : IsSumSq a := by
  obtain ⟨f, rfl⟩ := h
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    exact IsSumSq.sq_add (f 0) (ih fun i ↦ f i.succ)

theorem IsSumSq.exists_isSumSqOfLength {a : R} (h : IsSumSq a) : ∃ n, IsSumSqOfLength n a := by
  induction h with
  | zero => exact ⟨0, fun _ ↦ 0, by simp⟩
  | sq_add b _ ih =>
    obtain ⟨n, f, hf⟩ := ih
    refine ⟨n + 1, Fin.cons b f, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [hf]

theorem isSumSq_iff_exists_isSumSqOfLength {a : R} : IsSumSq a ↔ ∃ n, IsSumSqOfLength n a :=
  ⟨IsSumSq.exists_isSumSqOfLength, fun ⟨_, h⟩ ↦ h.isSumSq⟩

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

/-- Padding with zeros: a sum of `p` squares is a sum of `q` squares for every `q ≥ p`. -/
theorem IsSumSqOfLength.of_le {p q : ℕ} (hpq : p ≤ q) {a : R} (h : IsSumSqOfLength p a) :
    IsSumSqOfLength q a := by
  obtain ⟨f, rfl⟩ := h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  exact ⟨Fin.append f 0, by simp [Fin.sum_univ_add]⟩

theorem mem_pythagorasBounds_of_le {p q : ℕ} (hpq : p ≤ q) (hp : p ∈ pythagorasBounds R) :
    q ∈ pythagorasBounds R :=
  fun a ha ↦ (hp a ha).of_le hpq

end NonUnitalNonAssocSemiring

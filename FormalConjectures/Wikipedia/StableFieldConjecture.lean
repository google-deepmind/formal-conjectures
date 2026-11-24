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
# Stable field conjecture

A structure's first-order theory is model-theoretically stable when no partitioned formula defines
arbitrarily long finite half-graphs (Shelah's order property; see
`FirstOrder.Ring.IsStableRing`). Every algebraically closed field is stable in `Language.ring`
([Ma02, Example 4.1.14]; [Wikipedia: Stable theory](https://en.wikipedia.org/wiki/Stable_theory)).
Motivated by the classification of superstable fields [CS80], the **stable field conjecture**
(listed on [Wikipedia's unsolved problems list](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages))
states that any infinite field $K$ whose
theory in `Language.ring` is stable must be separably closed (`IsSepClosed K`). Finite fields are
excluded because every finite ring is automatically stable while no finite field is separably
closed.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages)
  (model-theory section, stating the stable field conjecture)
- [Wikipedia: Stable theory](https://en.wikipedia.org/wiki/Stable_theory)
  (order-property characterization and stability of algebraically closed fields)
- [CS80] G. Cherlin and S. Shelah, *Superstable fields and groups*, Ann. Math. Logic **18**
  (1980), no. 3, 227–270.
- [Ma02] D. Marker, *Model Theory: An Introduction*, Graduate Texts in Mathematics **217**,
  Springer, 2002, Example 4.1.14.
-/

@[expose] public section

namespace StableFieldConjecture

open FirstOrder FirstOrder.Language

/-- Every finite field is stable in `Language.ring`, witnessed here for `ZMod 2`. -/
@[category test, AMS 3 12]
theorem isStableRing_zmod_two : FirstOrder.Ring.IsStableRing (ZMod 2) :=
  FirstOrder.Ring.isStableRing_of_finite (ZMod 2)

/-- `ZMod 2` is not separably closed ($X^2 + X + 1$ is separable without roots in $\mathbb{F}_2$),
showing that the `[Infinite K]` hypothesis in `stable_field_conjecture` cannot be dropped. -/
@[category test, AMS 3 12]
theorem not_isSepClosed_zmod_two : ¬ IsSepClosed (ZMod 2) := by
  intro hsep
  obtain ⟨x, hx⟩ := @IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (ZMod 2) _ hsep 2
    1 1 1 (by decide) (by decide) (by decide)
  revert x hx
  decide

/-- The field $\mathbb{R}$ is not stable in `Language.ring`, witnessed by the order formula
$\varphi(x; y) :\equiv \exists z,\, x + z \cdot z = y$. -/
@[category test, AMS 3 12]
theorem not_isStableRing_real : ¬ FirstOrder.Ring.IsStableRing ℝ := by
  intro hstab
  let tx : Language.ring.Term ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) := Term.var (Sum.inl (Sum.inl 0))
  let ty : Language.ring.Term ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) := Term.var (Sum.inl (Sum.inr 0))
  let tz : Language.ring.Term ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) := Term.var (Sum.inr 0)
  let φ : Language.ring.Formula (Fin 1 ⊕ Fin 1) := BoundedFormula.ex ((tx + tz * tz).bdEqual ty)
  obtain ⟨n, hn⟩ := hstab 1 1 φ
  refine hn ⟨fun i _ => (i : ℝ), fun j _ => (j : ℝ), fun i j => ?_⟩
  simp only [φ, tx, ty, tz, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_bdEqual, FirstOrder.Ring.realize_add, FirstOrder.Ring.realize_mul,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, Fin.snoc_zero]
  constructor
  · rintro ⟨z, hz⟩
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by nlinarith [sq_nonneg z]
    exact Fin.le_iff_val_le_val.mpr (Nat.cast_le.mp hle)
  · intro hij
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_le.mpr (Fin.le_iff_val_le_val.mp hij)
    refine ⟨Real.sqrt (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)), ?_⟩
    linarith [Real.mul_self_sqrt (sub_nonneg.mpr hle)]

/-- The field $\mathbb{R}$ is not separably closed ($z^2 = -1$ has no real root). -/
@[category test, AMS 3 12]
theorem not_isSepClosed_real : ¬ IsSepClosed ℝ := by
  intro hsep
  obtain ⟨z, hz⟩ := @IsSepClosed.exists_eq_mul_self ℝ _ hsep (-1) inferInstance
  nlinarith [sq_nonneg z]

/-- Every algebraically closed field is model-theoretically stable in `Language.ring`
([Ma02, Example 4.1.14]; see [Wikipedia: Stable theory](https://en.wikipedia.org/wiki/Stable_theory)). -/
@[category textbook, AMS 3 12]
theorem isStableRing_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] :
    FirstOrder.Ring.IsStableRing K := by
  sorry

/-- **Stable field conjecture** ([CS80];
[Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages)).
Any infinite field $K$ that is stable in `Language.ring` is separably closed (`IsSepClosed K`). -/
@[category research open, AMS 3 12]
theorem stable_field_conjecture (K : Type*) [Field K] [Infinite K]
    (hK : FirstOrder.Ring.IsStableRing K) :
    IsSepClosed K := by
  sorry

end StableFieldConjecture

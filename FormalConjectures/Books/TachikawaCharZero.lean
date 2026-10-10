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
# Tachikawa's second conjecture in characteristic zero

The rational symmetric case asks whether vanishing positive self-Ext
forces finite-dimensional modules to be projective [Tac73, Section 8].

References:
- [Tac73] H. Tachikawa, *Quasi-Frobenius Rings and Generalizations*,
  Lecture Notes in Mathematics 351 (1973), Section 8.
  https://link.springer.com/chapter/10.1007/BFb0060005
- [Ki26] K. Kitamura, *A characteristic-zero Tachikawa counterexample* (2026).
  https://github.com/KitaKen1/tachikawa-characteristic-zero/tree/689ffa39ff4ddb5f8a6dadb50bd42d75a4bef825
-/

@[expose] public section

namespace TachikawaCharZero

/-- A $K$-algebra isomorphic to its dual as an $A$-bimodule. -/
def SymmetricOver (K A : Type) [Field K] [Ring A]
    [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

/-- The rational symmetric case of Tachikawa's second conjecture [Tac73, Section 8].
The answer is no [Ki26]. -/
@[category research solved, AMS 16,
    formal_proof using lean4 at "https://github.com/KitaKen1/tachikawa-characteristic-zero/blob/689ffa39ff4ddb5f8a6dadb50bd42d75a4bef825/lean/Tachikawa/Main.lean#L21"]
theorem tachikawaSecondConjecture :
    answer(False) ↔
      ∀ (Γ : Type) [Ring Γ] [Algebra ℚ Γ] [Module.Finite ℚ Γ],
        SymmetricOver ℚ Γ →
          ∀ (M : Type) [AddCommGroup M] [Module Γ M] [Module ℚ M]
            [IsScalarTower ℚ Γ M] [Module.Finite ℚ M],
            (∀ n : ℕ, 0 < n →
              Subsingleton (CategoryTheory.Abelian.Ext
                (ModuleCat.of Γ M) (ModuleCat.of Γ M) n)) →
              Module.Projective Γ M := by
  sorry

end TachikawaCharZero

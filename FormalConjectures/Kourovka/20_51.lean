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
# Conjecture 20.51

by D. MacHale

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v50), Problem 20.51.
-/

@[expose] public section

namespace Kourovka.«20.51»

/--
Is it true that for every odd integer $t > 3$ there exists a finite non-abelian group $G$ of odd
order with exactly $t$ conjugacy classes?
-/
@[category research open, question, AMS 20]
theorem kourovka_20_51 :
    ∀ t > 3, Odd t → ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a * b ≠ b * a) ∧
      Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = t := by
  sorry

end Kourovka.«20.51»

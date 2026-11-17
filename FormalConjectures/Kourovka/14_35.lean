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
# Conjecture 14.35

by N. D. Gupta

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300)
-/

@[expose] public section

namespace Kourovka.«14.35»

/--
Is every finitely presented group of prime exponent finite?
-/
@[category research open, question, AMS 20]
theorem kourovka_14_35 {G : Type*} [Group G]:
   Group.IsFinitelyPresented G ∧ Nat.Prime (Monoid.exponent G) → Finite G := by
  sorry

end Kourovka.«14.35»

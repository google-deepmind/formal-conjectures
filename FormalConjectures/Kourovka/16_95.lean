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
# Conjecture 16.95
By M. Sauerhering, M. Deissler
*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

@[expose] public section

namespace Kourovka.«16.95»
/--
If $ is a field and $A$ is in $GL(n,F)$, then there is a permutation matrix $P$ such that $AP$ is cyclic,
that is, the minimal polynomial of $AP$ is also its characteristic polynomial.
-/
@[category research open, AMS 20]
theorem kourovka_16_95 {F : Type*} [Field F] {n: Type*} [Fintype n] [DecidableEq n]:
    ∀ (A: Matrix n n F), A.rank = Fintype.card n →
    (∃(σ :Equiv.Perm n), minpoly ℝ (A * (σ.permMatrix ℝ))=(A * (σ.permMatrix ℝ)).charpoly)
 := by
  sorry

end Kourovka.«16.95»

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

import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
def A234642_condition (n x : ℕ) : Prop :=
  x.totient > 0 ∧ x % x.totient = n

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | A234642_condition n x}


theorem a_zero : a 0 = 1 := by
  delta a
  norm_num [ A234642_condition]
  exact IsLeast.csInf_eq ⟨ ⟨by constructor, rfl⟩, fun and' =>And.left⟩

theorem a_one : a 1 = 3 := by
  delta and a
  norm_num [A234642_condition]
  classical apply Nat.isLeast_find ⟨3,by decide⟩|>.csInf_eq

theorem a_two : a 2 = 10 := by
  norm_num[a]
  norm_num [A234642_condition]
  apply((Nat.isLeast_find ⟨10,by decide⟩ ) ).csInf_eq

theorem a_three : a 3 = 9 := by
  delta and a
  delta A234642_condition
  apply(Nat.isLeast_find ⟨9,by decide, rfl⟩).csInf_eq

/--
Conjecture: a(n) > 0 for all n. This would follow from a form of Goldbach's (binary) conjecture.
Checked up to 10^7; largest term in that range is a(9972987) = 4178506411.
-/
theorem oeis_a234642_conjecture_0 : ∀ (n : ℕ), a n > 0 := by
  sorry

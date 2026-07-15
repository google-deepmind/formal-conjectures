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

/-!
# A101779

`a(n)` is the least `k` such that all of `k, 2k+1, 3k+2, ..., nk+n-1` are primes, or `0` if no such `k` is found.
It is conjectured `k` always exists.

*Reference:* [A101779](https://oeis.org/A101779)
-/

namespace OeisA101779

open Nat Set
open scoped Nat.Prime

/--
A101779: `is_a101779_k n k` is true if for all $i$ from $1$ to $n$, $i \cdot k + (i - 1)$ is prime.
-/
def is_a101779_k (n k : ℕ) : Prop :=
  ∀ (i : ℕ), 1 ≤ i ∧ i ≤ n → (i * k + (i - 1)).Prime

/--
The primary defining sequence `a`.
$a(n)$ is the least $k$ such that all of $k, 2k+1, 3k+2, \ldots, nk+n-1$ are primes, or $0$ if no such $k$ is found.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | is_a101779_k n k }

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by
  push_cast [a]
  norm_num[is_a101779_k]
  apply Nat.isLeast_find ⟨2, by decide⟩ |>.csInf_eq

@[category test, AMS 11]
lemma test_a_2 : a 2 = 2 := by
  norm_num [a]
  delta is_a101779_k
  exact IsLeast.csInf_eq ⟨ fun and =>And.elim (by decide +revert), (·.one_mul▸. (1) (by decide) |>.two_le)⟩

@[category test, AMS 11]
lemma test_a_3 : a 3 = 3 := by
  norm_num [a]
  norm_num[is_a101779_k, Eq.comm]
  exact (IsLeast.csInf_eq (by use (by decide),fun a s => (one_mul a▸s (1) (by constructor) (by decide)).two_le.lt_of_ne (by cases· with((contradiction))))).symm

@[category test, AMS 11]
lemma test_a_4 : a 4 = 5 := by
  delta a
  norm_num[is_a101779_k]
  apply ((Nat.isLeast_find ⟨5,by decide⟩)).csInf_eq

/--
It is conjectured k always exists.
-/
@[category research open, AMS 11]
theorem main_conjecture : ∀ (n : ℕ), 1 ≤ n → ∃ k : ℕ, is_a101779_k n k := by
  sorry

end OeisA101779

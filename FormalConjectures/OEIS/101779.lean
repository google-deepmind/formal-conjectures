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

import FormalConjecturesUtil

/-!
# Conjectures associated with A101779

$a(n)$ is the least $k$ such that all of $k, 2k+1, 3k+2, ..., nk+n-1$ are primes,
or $0$ if no such $k$ is found.
It is conjectured $k$ always exists.

*References:*
- [A101779](https://oeis.org/A101779)
-/

namespace OeisA101779

open Nat Set
open scoped Nat.Prime

/--
A101779: `Ak n k` is true if for all $i$ from $1$ to $n$, $i \cdot k + (i - 1)$ is prime.
-/
def Ak (n k : ℕ) : Prop :=
  ∀ (i : ℕ), 1 ≤ i → i ≤ n → (i * k + (i - 1)).Prime

instance : DecidableRel Ak :=
  inferInstanceAs <| ∀ n k, Decidable <| ∀ (i : ℕ), 1 ≤ i → i ≤ n → (i * k + (i - 1)).Prime

/--
The primary defining sequence `a`.
$a(n)$ is the least $k$ such that all of $k, 2k+1, 3k+2, \ldots, nk+n-1$ are primes,
or $0$ if no such $k$ is found.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | Ak n k }

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := IsLeast.csInf_eq <| by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := IsLeast.csInf_eq <| by decide

/--
It is conjectured k always exists.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ (n : ℕ), 1 ≤ n → ∃ k : ℕ, Ak n k := by
  sorry

end OeisA101779

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
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }


/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by sorry

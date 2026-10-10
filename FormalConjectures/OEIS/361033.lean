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
# A factorial ratio analogous to the Catalan numbers

The sequence is defined by $a(n)=3(4n)!/(n!((n+1)!)^3)$ for $n \ge 0$.

*References:*
- [A361033](https://oeis.org/A361033)
- [Li26] Wentao Li, [Integrality and parity of a factorial ratio](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-formalization/A361033/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA361033

/-- The factorial ratio $3(4n)!/(n!((n+1)!)^3)$. -/
def a (n : ℕ) : ℕ :=
  3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3)

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 9 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 280 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 17325 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1513512 := by decide

/--
The parity conjecture:
"Conjecture: $a(n)$ is odd iff $n = 2^k - 1$ for some $k \ge 0$."
- Peter Bala, Mar 01 2023.

Proved and formalized in Lean by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewFormalization/A361033.lean#L380"]
theorem conjecture_1 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OeisA361033

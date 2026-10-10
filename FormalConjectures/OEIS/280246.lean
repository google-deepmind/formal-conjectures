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
# Product of sums of totatives over divisors

For $n \ge 1$, $a(n)$ is the product of the sums of totatives of all positive divisors of $n$.
The sum of totatives uses the positive integers at most the given integer, so its value at $1$
is $1$.

*References:*
- [A280246](https://oeis.org/A280246)
- [A023896](https://oeis.org/A023896)
- [Li26] Wentao Li, [A proof of the OEIS A280246 conjecture](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A280246/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA280246

/-- The sum of totatives of $m$, as in A023896, with value $1$ at $m = 1$. -/
def sumTotatives (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m with k.Coprime m, k

/-- The product of the sums of totatives over all positive divisors of $n$. -/
def a (n : ℕ) : ℕ :=
  ∏ d ∈ n.divisors, sumTotatives d

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 10 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 18 := by decide

/--
"Conjecture: $a(n)$ is odd iff the sum of totatives of $n$ (A023896) is odd."
- OEIS A280246, entry by Jaroslav Krizek, Dec 30 2016.

The OEIS sequence starts at $n = 1$.
Proved and formalized in Lean by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A280246.lean#L315"]
theorem conjecture (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ Odd (sumTotatives n) := by
  sorry

end OeisA280246

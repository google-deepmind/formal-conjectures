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
# OEIS A361717, Bala's Conjecture 2

Peter Bala defines $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$ (offset 0,
$a(0) = 0$). Conjecture 2 (Mar 2023): $a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$ for every prime
$p \ne 3$.

*References:*
- Peter Bala, [A361717](https://oeis.org/A361717), Mar 26, 2023.
-/

@[expose] public section

namespace OeisA361717

/-- OEIS A361717: $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$. -/
def a361717 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k ^ 2 * (n + k).choose k

/-- Bala (A361717, Conjecture 2): for every prime $p \ne 3$,
$a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem a361717_conj2 (p : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    (a361717 (p - 1) : ℤ) ≡ 1 - 2 * p - p ^ 2 [ZMOD p ^ 3] := by
  sorry

end OeisA361717

end

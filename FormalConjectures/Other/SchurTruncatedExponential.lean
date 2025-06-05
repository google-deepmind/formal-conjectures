/-
Copyright 2025 The Formal Conjectures Authors.

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
# Schur's theorem on Galois groups of truncated exponential polynomials

*Reference:* (https://math.stackexchange.com/questions/2814220)

*Reference* (https://mathoverflow.net/questions/477077)
-/

/-
Note: This was asked by Nick Katz. Quasi-autoformalized using Claude 4.0 Sonnet.
-/

open Polynomial

open scoped Nat

/--
The truncated exponential polynomial `truncatedExp n` is
given by `∑_{j=0}^{n} x^j / j!` over `ℚ`, which is the
`n`-th partial sum of the Taylor series for the exponential function `e^x`.
-/
noncomputable def truncatedExp (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), (1 / j ! : ℚ) • X ^ j

/--
**Schur's Theorem (1924):**
Let `f_n(x) = ∑_{j=0}^n x^j/j!` be the `n`-th truncated
exponential polynomial over `ℚ`. Then for `n ≥ 2`:

- If `n ≡ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the alternating group `A_n`
- If `n ≢ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the symmetric group `S_n`
-/
@[category research solved, AMS 12]
theorem schur_truncatedExp_galoisGroup_equiv (n : ℕ) (hn : n ≥ 2) :
  letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)) := by
  sorry

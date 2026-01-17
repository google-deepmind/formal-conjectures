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
# Erdős Problem 275

*References:*
- [erdosproblems.com/270](https://www.erdosproblems.com/270)
- [CrVE70] R.B. Crittenden and C.L. Vanden Eynden, *Any n arithmetic progressions covering the first
  2^n integers cover all integers*, Proc. Amer. Math. Soc. 24 (1970), 475-481.
-/

open Set

namespace Erdos275

/--
A system of $r$ congruences $\{(a_i, n_i)\}_{i=1}^r$ covers an integer $x$ if $x \equiv a_i
\pmod{n_i}$ for some $i$.
-/
def isCoveredBy {r : ℕ} (a : Fin r → ℤ) (n : Fin r → ℕ) (x : ℤ) : Prop :=
  ∃ i, x ≡ a i [ZMOD n i]

/--
If a finite system of $r$ congruences $\{ a_i\pmod{n_i} : 1\leq i\leq r\}$ (the $n_i$ are not
necessarily distinct) covers $2^r$ consecutive integers then it covers all integers.

This is best possible as the system $2^{i-1}\pmod{2^i}$ shows. This was proved indepedently by
Selfridge and Crittenden and Vanden Eynden [CrVE70].
-/
@[category research solved, AMS 11]
theorem erdos_275 (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ) :
    (∃ k : ℤ, ∀ x ∈ Ico k (k + 2 ^ r), isCoveredBy a n x) →
    (∀ x : ℤ, isCoveredBy a n x) := by
  sorry

end Erdos275

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
# Determinantal conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Determinantal_conjecture)
-/

/- Formalisation note: Here, we represent the two normal matrices as $U_1 D_1 U_1^*$ and
$U_2 D_2 U_2^*$ respectively, where $U_1, U_2$ are unitary and $D_1, D_2$
are diagonal. This is an universal form of a normal matrix,
allowing to retrieve $\lambda (A)_i$ as ${D_1}_{i,i}$, whereas the current mathlib
doesn't support obtaining the vector of eigenvalues from a general normal
non-Hermitian matrix. -/

namespace DeterminantalConjecture

/--
Does the determinant of the sum $A + B$ of two $n \times n$ normal
complex matrices A and B always lie in the convex hull
of the $n!$ points $\prod i (\lambda(A)_i + \lambda(B)_{σ(i)})$?
Here the numbers $\lambda (A)_i$ and $\lambda (B)_i$ are
the eigenvalues of $A$ and $B$, and $\sigma$ is an element of the symmetric
group $S_n$.
-/
@[category research open, AMS 15]
theorem determinantal_conjecture
    (n : Type) [Fintype n] [DecidableEq n]
    (d1 d2 : n → ℂ) (U1 U2 : unitary (Matrix n n ℂ)) :
    (U1 * Matrix.diagonal d1 * star U1 + U2 * Matrix.diagonal d2 * star U2).det
      ∈ convexHull ℝ { ∏ i, (d1 i + d2 (σ i)) | σ : Equiv.Perm n } := by
  sorry

end DeterminantalConjecture

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
# Noncollapse of the polynomial hierarchy

*References:*
* Arora–Barak, *Computational Complexity: A Modern Approach*, author draft
  dated 2007-01-08, Definition 5.4 and §5.2.1, p. 5.3 (93),
  https://theory.cs.princeton.edu/complexity/book.pdf.
-/

namespace AroraBarak

open ComplexityTheory

/-- **Polynomial-hierarchy noncollapse** (Arora–Barak, §5.2.1): every existential
level $\Sigma_k^P$ is strictly contained in $\Sigma_{k+1}^P$, for every finite
$k\ge0$. Level zero is $P$. Positive levels use exactly $k$ alternating quantifier
blocks, starting existentially, each of a fixed polynomial length in the bit-string
input, followed by a polynomial-time TM2 verifier. Later choices may depend on
earlier blocks. Level one uses exact-length certificates and is not definitionally
the imported $NP$. Under the standard class identifications, noncollapse implies
$P\ne NP$. -/
@[category research open, AMS 3 68]
theorem polynomialHierarchy_strict : ∀ k : ℕ, SigmaP k ⊂ SigmaP (k + 1) := by sorry

end AroraBarak

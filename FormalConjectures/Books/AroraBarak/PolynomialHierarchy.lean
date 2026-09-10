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

Reference: Arora–Barak, *Computational Complexity: A Modern Approach*, Chapter 5.
The author draft dated 2007-01-08 states the conjecture in §5.2.1, p.5.3 (93),
immediately after Definition 5.4:
https://theory.cs.princeton.edu/complexity/book.pdf.

Levels are defined by a fixed number of alternating polynomial-length quantifier
blocks and an actual polynomial-time TM2 verifier. Level zero is P.
-/

namespace AroraBarak

open ComplexityTheory

/-- Every existential level of the polynomial hierarchy is strictly contained in
the next level. In particular, the hierarchy does not collapse at any finite level. -/
@[category research open, AMS 3 68]
theorem polynomialHierarchy_strict : ∀ k : ℕ, SigmaP k ⊂ SigmaP (k + 1) := by sorry

end AroraBarak

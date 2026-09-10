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
# Unique Games and perfect-completeness 2-to-1 Games

Reference: V. Guruswami, S. Khot, R. O'Donnell, P. Popat, M. Tulsiani and Y. Wu,
*SDP gaps for 2-to-1 and other Label-Cover variants*, ICALP 2010,
Definitions 1–2 and Conjectures 1–2, pp.2–3:
https://www.cs.cmu.edu/~odonnell/papers/2-to-1-gaps.pdf.

We use that paper's total projections with fibers of size at most d and equal
alphabets. The alphabet size is a constant chosen after the gap parameters,
before the input. Rational gaps are cofinal in the positive real gaps.
The inequalities require disjoint yes and no regions.
-/

namespace GuruswamiEtAl2010

open ComplexityTheory Computability.LabelCover

/-- Unique Games: distinguishing value at least $1-\varepsilon$ from value at
most $\delta$ is NP-hard for a sufficiently large fixed alphabet. -/
@[category research open, AMS 5 68]
theorem unique_games :
    ∀ ε δ : ℚ, 0 < ε → 0 < δ → ε + δ < 1 →
      ∃ q : ℕ, 0 < q ∧ PromiseNPHard (Yes 1 q (1 - ε)) (No 1 q δ) := by sorry

/-- The 2-to-1 Games Conjecture with perfect completeness: distinguish value
exactly one from value at most $\delta$. This does not assert the already proved
variant with completeness arbitrarily close to one. -/
@[category research open, AMS 5 68]
theorem two_to_one_perfect :
    ∀ δ : ℚ, 0 < δ → δ < 1 →
      ∃ q : ℕ, 0 < q ∧ PromiseNPHard (Yes 2 q 1) (No 2 q δ) := by sorry

end GuruswamiEtAl2010

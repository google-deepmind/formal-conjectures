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
# Randomized fine-grained complexity hypotheses

Reference: Virginia Vassilevska Williams, *On some fine-grained questions in
algorithms and complexity*, ICM 2018:
https://people.csail.mit.edu/virgi/eccentri.pdf.

We state Hypotheses 1, 2, 4 (k=2) and 8 (k=3). Algorithms use the source's
randomized word-RAM model with logarithmic word size, made explicit by a finite
instruction list and an operational interpreter. Error probability is at most 1/3.
Rational exponents express the positive constant savings in the hypotheses.

For the three-distinct-elements convention in 3SUM, see Dudek, Gawrychowski
and Starikovskaya, *All non-trivial variants of 3-LDT are equivalent*,
arXiv:2001.01289v1, §1, pp.2–3:
https://arxiv.org/pdf/2001.01289v1.
-/

namespace VassilevskaWilliams2018

open FineGrained WordRAM

/-- Randomized SETH: for every rational rate below one, some fixed clause width
admits no algorithm with that exponential rate, even allowing a polynomial
factor in the encoded formula length. -/
@[category research open, AMS 68]
theorem randomized_SETH :
    ∀ a b : ℕ, 0 < b → a < b → ∃ k : ℕ, 3 ≤ k ∧ ¬ HasSatTime k a b := by sorry

/-- Integer 3SUM on n distinct integers in $[-n^4,n^4]$ has no randomized
truly subquadratic algorithm. -/
@[category research open, AMS 68]
theorem integer_threeSum :
    ∀ a b : ℕ, 0 < b → a < 2 * b →
      ¬ HasPowerTimeDecider ValidThreeSum threeSum List.length (fun _ => 1) a b := by sorry

/-- Orthogonal Vectors has no randomized truly subquadratic algorithm in the
number of vectors, even allowing a polynomial factor in dimension. -/
@[category research open, AMS 68]
theorem orthogonal_vectors :
    ∀ a b : ℕ, 0 < b → a < 2 * b → ¬ HasOVTime a b := by sorry

/-- Exact Triangle: detecting a weight-zero triangle in an n-vertex graph with
edge weights in $[-n^{300},n^{300}]$ has no randomized truly subcubic algorithm.
This is Hypothesis 8 for k=3, with the source's exponent 100k. -/
@[category research open, AMS 5 68]
theorem exact_triangle :
    ∀ a b : ℕ, 0 < b → a < 3 * b →
      ¬ HasPowerTimeDecider (ValidWeightedGraph 300) exactTriangle
        List.length (fun _ => 1) a b := by sorry

end VassilevskaWilliams2018

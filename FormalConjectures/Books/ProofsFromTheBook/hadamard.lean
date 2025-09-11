/-
Copyright 2025 Google LLC

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

-- TODO(firsching): consider providing a different source? Perhaps a primary one?
/--
From "Proofs from THE BOOK", by Martin Aigner and Günter M. Ziegler (6th edition)

A version of the Hadamard conjecture as stated on page 44, chapter 7:

|A| ≤ n^{n/2}.

When do we have equality?
[...]
Matrices A with ±1-entries that achieve equality are aptly called
\textit{Hadamard matrices}.
-/
def IsHadamard (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    Matrix.det M = n ^ ((n : ℝ) / 2)

/--
Does a Hadamard matrix exist for all n = 4a? No one knows.
-/
@[problem_status open]
theorem HadamardConjecture (k : ℕ) : ∃ M, IsHadamard (4 * k) M := sorry

/--
The answer is yes for \(n\) up to the current record n = 664.
The first unknown case 668 = 4 * 167
-/
@[problem_status open]
theorem HadamardConjecture.variant : ∃ M, IsHadamard (4 * 167) M := sorry

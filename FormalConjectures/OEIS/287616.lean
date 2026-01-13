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
# Sum of a triangular number, a generalized pentagonal number, and a generalized heptagonal number

Any nonnegative integer can be written as $x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2$ with $x, y, z$
nonnegative integers.

Zhi-Wei Sun has offered a USD 135 prize for the first proof of this conjecture.

*References:* 
- [OEIS A287616](https://oeis.org/A287616)
- Zhi-Wei Sun, "Universal sums of three quadratic polynomials", arXiv:1502.03056 [math.NT]
-/

namespace OeisA287616

/-- The predicate that `n` can be written as $x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2$ for
nonnegative integers $x, y, z$. -/
def IsSumOfTriangularAndGeneralizedPolygonal (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (3 * y + 1) / 2 + z * (5 * z + 1) / 2

@[category test, AMS 11]
theorem isSumOfTriangularAndGeneralizedPolygonal_0 :
    IsSumOfTriangularAndGeneralizedPolygonal 0 :=
  ⟨0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfTriangularAndGeneralizedPolygonal_1 :
    IsSumOfTriangularAndGeneralizedPolygonal 1 :=
  ⟨1, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfTriangularAndGeneralizedPolygonal_2 :
    IsSumOfTriangularAndGeneralizedPolygonal 2 :=
  ⟨0, 1, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfTriangularAndGeneralizedPolygonal_4 :
    IsSumOfTriangularAndGeneralizedPolygonal 4 :=
  ⟨1, 0, 1, by norm_num⟩

/--
**Zhi-Wei Sun's Conjecture (A287616)**: Any nonnegative integer can be written as the sum of
a triangular number $x(x+1)/2$, a generalized pentagonal number $y(3y+1)/2$, and a generalized
heptagonal number $z(5z+1)/2$, where $x, y, z$ are nonnegative integers.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : IsSumOfTriangularAndGeneralizedPolygonal n := by
  sorry

end OeisA287616

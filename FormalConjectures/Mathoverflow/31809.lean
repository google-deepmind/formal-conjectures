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
module

public import FormalConjecturesUtil

/-!
# Mathoverflow 31809

Source:
[Mathoverflow/31809](https://mathoverflow.net/questions/31809/pre-triangulated-category-that-isnt-triangulated)

*References:*
- [CLLZ26] X.-W. Chen, J. Liu, X.-S. Lu and C. Zhang, "A pre-triangulated category which is not
  triangulated", [arXiv:2608.09777](https://arxiv.org/abs/2608.09777)
-/

@[expose] public section

namespace Mathoverflow31809

open CategoryTheory Limits Category Preadditive Pretriangulated

/-- Does there exist a category that is pretriangulated but not triangulated?

Yes. Theorem 1.2 of [CLLZ26] twists the triangulated structure on the category of finitely
generated projective modules over the preprojective algebra of type $A_5$ over $\mathbb{F}_2$.
The result is pretriangulated but does not satisfy the octahedral axiom.
-/
@[category research solved, AMS 18]
theorem mathoverflow_31809 : answer(True) ↔ ¬ (∀ (C : Type*) [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C], IsTriangulated C) := by
  sorry

end Mathoverflow31809

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
# Mathoverflow 31908

Source:
[Mathoverflow/31908](https://mathoverflow.net/questions/31809/pre-triangulated-category-that-isnt-triangulated)

-/

namespace Mathoverflow31809

open CategoryTheory Limits Category Preadditive Pretriangulated

/-- Does there exist a category that is pretriangulated but not triangulated? -/
@[category research open, AMS 18]
theorem mathoverflow_31809 : (∀ (C : Type*) [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C], ¬ IsTriangulated C) ↔ answer(sorry) := by
  sorry

end Mathoverflow31809

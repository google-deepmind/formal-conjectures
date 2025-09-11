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

/--
From "Unsolved Problems in Intuitive Geometry", by Viktor Klee.

Problem K3.

Suppose I is a closed interval of real numbers, and f and g are commuting
continuous maps of I into itself. Must they have a common fixed point?
-/
@[problem_status open]
theorem K3 {a b : ℝ} (f g : (Set.Icc a b) → (Set.Icc a b))
    (h: ∀ z, f (g z) = g (f z)) (hf : Continuous  f) (hg : Continuous g) :
    ∃ x, (f x = x ∧ g x = x) := sorry

-- TODO(firsching):  Add a "non-subtype" formalisation of this problem
-- (i.e. with f and g defined over the whole of R and using ContinousOn, etc).
-- Then also including the statetement that the two formalisations are equivalent

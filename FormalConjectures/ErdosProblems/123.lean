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
# Erdős Problem 123

*Reference:* [erdosproblems.com/123](https://www.erdosproblems.com/123)
-/

namespace Erdos123

/-- Let a,b,c be three integers which are pairwise coprime. Is every large integer the sum of distinct integers of the form akblcm (k,l,m≥0), none of which divide any other?

ANSWER
-/
theorem erdos_123

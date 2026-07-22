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
# Numbers n such that phi(n) = phi(n + phi(n))

The sequence A108569 consists of numbers $n$ such that $\phi(n) = \phi(n + \phi(n))$.

*References:*
- [A108569](https://oeis.org/A108569)
-/

namespace OeisA108569

/--
The primary defining sequence `a`.
`a n` is the $(n+1)$-th positive integer $k$ such that $\phi(k) = \phi(k + \phi(k))$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth (fun k ↦ 0 < k ∧ k.totient = (k + k.totient).totient)

/-- Conjecture: Except for the first term all terms are even. -/
@[category research open, AMS 11]
theorem conjecture : ∀ n, 0 < n → Even (a n) := by
  sorry

end OeisA108569

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

import FormalConjectures.Util.ProblemImports

/-!
# Primitive roots of the form k² + 1

Every prime $p$ has a primitive root $0 < g < p$ of the form $k^2 + 1$, where $k$ is an integer.

Zhi-Wei Sun has offered a prize of RMB 2,000 for the first proof.

*References:*
- [OEIS A239957](https://oeis.org/A239957)
- Z.-W. Sun, "New observations on primitive roots modulo primes," arXiv:1405.0290 [math.NT], 2014.
-/

namespace OEIS.A239957

/--
**Zhi-Wei Sun's Conjecture (A239957)**: Every prime $p$ has a primitive root $0 < g < p$ of the
form $k^2 + 1$, where $k$ is an integer.
-/
@[category research open, AMS 11]
theorem conjecture (p : ℕ) (hp : p.Prime) :
    ∃ k : ℤ, k ^ 2 + 1 < p ∧
      orderOf (k ^ 2 + 1 : ZMod p) = p - 1 := by
  sorry

end OEIS.A239957

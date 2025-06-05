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
# Andrica's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Andrica%27s_conjecture)
-/

/--
The inequality $\sqrt{p_{n+1}}-\sqrt{p_n} < 1$ holds for all $n$, where $p_n$ is the nth prime number.
-/
@[category research open, AMS 11]
theorem andrica_conjecture (n : ℕ) :
    Real.sqrt ((n+1).nth Prime) - Real.sqrt (n.nth Prime) < 1 := by
  sorry

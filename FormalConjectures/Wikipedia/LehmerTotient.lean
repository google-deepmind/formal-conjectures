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
# Lehmer's totient problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Lehmer%27s_totient_problem)
-/

/--
Does there exist a composite number $n > 1$ such that Euler’s totient function
$\varphi(n)$ divides $n - 1$?
-/
@[category research open, AMS 11]
theorem lehmer_totient :
    (∃ n > 1, ¬Prime n ∧ Nat.totient n ∣ n - 1) ↔ answer(sorry) := by
  sorry

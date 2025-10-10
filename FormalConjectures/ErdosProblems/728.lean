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
# Erdős Problem 728

*Reference:* [erdosproblems.com/728](https://www.erdosproblems.com/728)
-/

namespace Erdos728

/--
Let $\varepsilon, C > 0$.
Are there integers $a, b, n$ such that

$$
a > \varepsilon n,\quad b > \varepsilon n, \quad
a!\, b! \mid n!\, (a + b - n)!,
$$

and

$$
a + b > n + C \log n ?
$$
-/
@[category research open, AMS 11]
theorem erdos_728 (ε C : ℝ) :
    ∃ a b n : ℕ,
      ε * n < a ∧
      ε * n < b ∧
      Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
      a + b > n + C * Real.log n := by
  sorry

-- TODO(firsching): Use Legendre's formula to test divisibility in terms of p-adic valuations.

end Erdos728

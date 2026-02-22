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

open Real
open scoped Nat Topology

namespace Erdos728

/--
Let $\varepsilon$ be sufficiently small and $C, C' > 0$. Are there integers $a, b, n$ such that
$$a, b > \varepsilon n\quad a!\, b! \mid n!\, (a + b - n)!, $$
and
$$C \log n < a + b - n < C' \log n ?$$

Note that the website currently displays a simpler (trivial) version of this problem because
$a + b$ isn't assumed to be in the $n + O(\log n)$ regime.

Barreto and ChatGPT-5.2 have proved that, for any $0 < C_1 < C_2$, there are infinitely many
$a, b, n$ with $b = n/2$, $a = n/2 + O(\log n)$, and $C_1 \log n < a + b - n < C_2 \log n$ such
that $a! b! \mid n! (a + b - n)!$

This appears to answer the question in the spirit it was intended.
-/
@[category research solved, AMS 11]
theorem erdos_728 :
    answer(True) ↔
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
        ∃ a b n : ℕ,
          0 < n ∧
          ε * n < a ∧
          ε * n < b ∧
          a ! * b ! ∣ n ! * (a + b - n)! ∧
          a + b > n + C * log n ∧
          a + b < n + C' * log n := by
  sorry

-- TODO(firsching): Use Legendre's formula to test divisibility in terms of p-adic valuations.

end Erdos728

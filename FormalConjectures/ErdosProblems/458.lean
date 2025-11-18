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
# Erdős Problem 458
*Reference:* [erdosproblems.com/458](https://www.erdosproblems.com/458)
-/

namespace Erdos458

/--
least common multiple of ${1, \cdots, n}$
-/
def lcm_upto (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/--
Let $lcm(1, \cdots, n)$ denote the least common multiple of ${1, \cdots, n}$.
And $p_{k}$ the $k$th prime.
Is it true that, for all $k \geq 1$, $lcm(1, \cdots, p_{k+1}−1) < p_{k} * lcm(1, \cdots, p_{k})$ ?
-/
@[category research open, AMS 11]
theorem erdos_458 :
    (∀ k : ℕ, lcm_upto ((k + 1).nth Prime - 1)
     < k.nth Prime * lcm_upto (k.nth Prime)) ↔ answer(sorry) := by
    sorry

end Erdos458

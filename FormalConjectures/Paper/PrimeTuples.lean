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
# Prime Tuples Conjecture

*Reference:* [FLC07] Friedlander, J. B. and Luca, F. and Stoiciu, M., On the irrationality of a
divisor function series. Integers (2007).
-/

open Nat

namespace PrimeTuplesConjecture

/-- For any `k ≥ 2`, let `a₁,...,aₖ` and `b₁,...,bₖ` be integers with `aᵢ > 0`. Suppose that for
every prime `p` there exists an integer `n` such that `p ∤ ∏ i, (aᵢ n + bᵢ)`. Then there exist
infinitely many `n` such that `aᵢ n + bᵢ` is prime for all `i`. -/
@[category research open, AMS 11]
theorem prime_tuples_conjecture {k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℕ+) (b : Fin k → ℕ)
    (hab : ∀ p, p.Prime → ∃ n, ¬ p ∣ ∏ i, (a i * n + b i)) :
    Set.Infinite {n | ∀ i : Fin k, (a i * n + b i).Prime} := by sorry

end PrimeTuplesConjecture

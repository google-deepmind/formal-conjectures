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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 555

*Reference:* [erdosproblems.com/555](https://www.erdosproblems.com/555)

Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured
then there is a monochromatic copy of $G$. Determine the value of
\[R_k(C_{2n}).\]
-/

namespace Erdos555

open SimpleGraph

/--
The Ramsey number `R_k(G)` : the least integer `m` such that every `k`-colouring of
the edges of the complete graph on `m` vertices contains a monochromatic copy of `G`.
-/
noncomputable def ramseyNumber {α : Type*} (k : ℕ) (G : SimpleGraph α) : ℕ := sorry

/--
The cycle graph on `2n` vertices.
-/
def cycle (n : ℕ) : SimpleGraph (Fin (2 * n)) := sorry

/--
A known lower bound for the Ramsey number of even cycles:
\[
R_k(C_{2n}) \ge (k-1)(2n-1)+1.
\]
This bound is elementary (by considering a certain colouring).
The exact value is a difficult open problem in general.
-/
@[category research open, AMS 52]
theorem erdos_555 (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ramseyNumber k (cycle n) ≥ (k - 1) * (2 * n - 1) + 1 := by
  sorry

-- TODO(firsching): formalize other results from the additional material

end Erdos555

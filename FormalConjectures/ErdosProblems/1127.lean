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
# Erdős Problem 1127

*Reference:* [erdosproblems.com/1127](https://www.erdosproblems.com/1127)

[ErKa43] Erdős, P. and Kakutani, S., *On non-denumerable graphs*, Bull. Amer. Math. Soc. 49
(1943), 457-461.

[Da72] Davies, R. O., *Partitioning the plane into denumerably many sets without repeated
distances*, Proc. Cambridge Philos. Soc. 72 (1972), 179-183.

[Ku87] Kunen, K., *Partitioning Euclidean space*, Math. Proc. Cambridge Philos. Soc. 102 (1987),
379-383.
-/

namespace Erdos1127

/--
Can $\mathbb{R}^n$ be decomposed into countably many sets, such that within each set all the
pairwise distances are distinct?

This is true assuming the continuum hypothesis for $n = 1$ (Erdős-Kakutani [ErKa43]),
for $n = 2$ (Davies [Da72]), and for all $n$ (Kunen [Ku87]). The dependence on the
continuum hypothesis is necessary by a result of Erdős and Hajnal.
-/
@[category research solved, AMS 3 5]
theorem erdos_1127 : answer(sorry) ↔
    ∀ n : ℕ, ∃ f : EuclideanSpace ℝ (Fin n) → ℕ,
      ∀ a b c d : EuclideanSpace ℝ (Fin n),
        f a = f b → f a = f c → f a = f d →
        a ≠ b → c ≠ d →
        dist a b = dist c d →
        ({a, b} : Set (EuclideanSpace ℝ (Fin n))) = {c, d} := by
  sorry

end Erdos1127

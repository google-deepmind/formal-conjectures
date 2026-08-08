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
# Erdős Problem 260

*References:*
- [erdosproblems.com/260](https://www.erdosproblems.com/260)
- [Wang--Grau Ribas, *Positive dyadic density for rational weighted binary expansions*]
  (https://arxiv.org/abs/2606.24972)
-/

namespace Erdos260

open Filter

/--
Let $a_1 < a_2 < \cdots$ be an increasing sequence such that $\frac{a_n}{n} \to \infty$.
Is the sum $\sum_{n}^{\infty} \frac{a_n}{2^{a_n}}$ irrational?
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/Hanziwww/erdos260/blob/1f2baf4547f2c2805cdd160611b0b983f43941aa/Erdos260/DeepMind.lean#L92-L132"]
theorem erdos_260 : answer(True) ↔
                  ∀ a : ℕ → ℤ, ∀ s : ℝ,
                  StrictMono a →
                  Tendsto (fun n => (a n : ℝ ) / n ) atTop atTop →
                  HasSum (fun n => (a n : ℝ ) / 2 ^ a n) s → Irrational s :=
  sorry

-- TODO: Add a proof of the theorem under the strong assumption $a_{n+1}-a_n → \infty$
-- TODO: Add a proof of the theorem under the strong assumption $a_n \gg n\sqrt{\log{n}\log{\log{n}}}$

end Erdos260

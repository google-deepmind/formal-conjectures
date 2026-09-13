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
# Erdős Problem 820

*Reference:* [erdosproblems.com/820](https://www.erdosproblems.com/820)
-/

open Filter Real
open scoped Topology

namespace Erdos820

/-- $H(n)$ is the smallest integer $l$ such that there exist $k<l$ with
$(k^n-1,l^n-1)=1$. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { l : ℕ | ∃ k, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1) }

/--
Let $H(n)$ be the smallest integer $l$ such that there exist $k<l$ with $(k^n-1,l^n-1)=1$.
Is it true that $H(n)=3$ infinitely often? (That is, $(2^n-1,3^n-1)=1$ infinitely often?)
-/
@[category research open, AMS 11]
theorem erdos_820.parts.i :
    answer(sorry) ↔ { n : ℕ | H n = 3 }.Infinite := by
  sorry

/--
Estimate $H(n)$. Is it true that there exists some constant $c>0$ such that, for all
$\epsilon>0$,
$$
H(n) > \exp(n^{(c-\epsilon)/\log\log n})
$$
for infinitely many $n$ and
$$
H(n) < \exp(n^{(c+\epsilon)/\log\log n})
$$
for all large enough $n$?
-/
@[category research open, AMS 11]
theorem erdos_820.parts.ii :
    answer(sorry) ↔
      ∃ c > (0 : ℝ), ∀ ε > 0,
        { n : ℕ | exp (n ^ ((c - ε) / log (log n))) < H n }.Infinite ∧
          ∀ᶠ n : ℕ in atTop, (H n : ℝ) < exp (n ^ ((c + ε) / log (log n))) := by
  sorry

end Erdos820

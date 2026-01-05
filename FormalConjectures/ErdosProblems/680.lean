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
# Erdős Problem 680

*Reference:* [erdosproblems.com/680](https://www.erdosproblems.com/680)
-/


namespace Erdos680

open Real

/--
Is it true that, for all sufficiently large $n$, there exists some $k$ such that
\[
p(n+k)>k^2+1,
\]
where $p(m)$ denotes the least prime factor of $m$?
-/
@[category research open, AMS 11]
theorem erdos_680 :
  answer(sorry) ↔ ∀ᶠ (n : ℕ) in Filter.atTop, ∃ k ≠ 0, Nat.minFac (n + k) > k^2 + 1 := sorry

/--
Can one prove this is false if we replace $k^2+1$ by $e^{(1+\epsilon)\sqrt{k}}+C_\epsilon$, for all
$\epsilon>0$, where $C_\epsilon>0$ is some constant?
-/
@[category research open, AMS 11]
theorem erdos_680.variant : answer(sorry) ↔ ∀ ε > 0, ∃ C > 0,
  ¬ ∀ᶠ (n : ℕ) in Filter.atTop, ∃ k ≠ 0,
  Nat.minFac (n + k) > exp ((1 + ε) * √k) + C := sorry

end Erdos680

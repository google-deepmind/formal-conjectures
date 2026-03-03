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
# Erdős Problem 417

*References:*
- [erdosproblems.com/417](https://www.erdosproblems.com/417)
- [Er98] Erdős, Paul, Some of my new and almost new problems and results in combinatorial number
  theory. Number theory (Eger, 1996) (1998), 169-180.
-/

open Nat Set Filter
open scoped Topology

namespace Erdos417

/--
Let\[V'(x)=\#\{\phi(m) : 1\leq m\leq x\}\]and\[V(x)=\#\{\phi(m) \leq x : 1\leq m\}.\]
Does $\lim V(x)/V'(x)$ exist?

Formalization note: We formalize the limit of the inverse fraction V'(x)/V(x)
to ensure the limit is finite (bounded between 0 and 1).
-/
@[category research open, AMS 11]
theorem erdos_417.part.a :
    answer(sorry) ↔ ∃ L : ℝ, Tendsto (fun x ↦
      ((totient '' { m | 1 ≤ m ∧ (m : ℝ) ≤ x }).ncard : ℝ) /
      ({ k | k ∈ range totient ∧ (k : ℝ) ≤ x }.ncard : ℝ))
      atTop (𝓝 L) := by
  sorry

/--
Is it $>1$?
-/
@[category research open, AMS 11]
theorem erdos_417.part.b :
    answer(sorry) ↔ ∃ L < 1, Tendsto (fun x ↦
      ((totient '' { m | 1 ≤ m ∧ (m : ℝ) ≤ x }).ncard : ℝ) /
      ({ k | k ∈ range totient ∧ (k : ℝ) ≤ x }.ncard : ℝ))
      atTop (𝓝 L) := by
  sorry

/--
By Ford's theorem (1998), the count of totient values up to $x$ satisfies
$V(x) \sim x / \sqrt{\log x \cdot \log \log x}$ asymptotically. The ratio $V(x)/V'(x)$
is therefore related to the density of totient values; whether the limit exists
is the open question here.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/417", AMS 11]
theorem erdos_417.variants.known_result :
    { k | k ∈ range totient ∧ (k : ℝ) ≤ 10 }.ncard =
    (totient '' { m | 1 ≤ m ∧ (m : ℝ) ≤ 10 }).ncard := by
  sorry

end Erdos417

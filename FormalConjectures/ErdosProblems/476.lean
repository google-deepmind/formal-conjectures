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
# Erdős Problem 476

For a prime $p$ and $A \subseteq \mathbb{F}_p$, the restricted sumset
$A \hat{+} A = \{a + b : a, b \in A, a \neq b\}$ satisfies
$|A \hat{+} A| \geq \min(2|A| - 3, p)$.

*Reference:* [erdosproblems.com/476](https://www.erdosproblems.com/476)

[dSHa94] da Silva, J.A.D. and Hamidoune, Y.O., *Cyclic spaces for Grassmann derivatives and
additive theory*, Bull. London Math. Soc. 26 (1994), 140-146.
-/

open Finset

namespace Erdos476

/--
The restricted sumset $A \hat{+} A = \{a + b : a, b \in A, a \neq b\}$, consisting of all
pairwise sums of distinct elements from $A$.
-/
def restrictedSumset {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.biUnion (fun a => (A.erase a).image (fun b => a + b))

/--
Erdős-Heilbronn Conjecture (Problem 476):

Let $p$ be a prime and let $A \subseteq \mathbb{F}_p$. Define the restricted sumset
$$A \hat{+} A = \{a + b : a, b \in A, a \neq b\}.$$
Is it true that $|A \hat{+} A| \geq \min(2|A| - 3, p)$?

A question of Erdős and Heilbronn. Solved in the affirmative by
da Silva and Hamidoune [dSHa94].
-/
@[category research solved, AMS 5 11]
theorem erdos_476 : answer(True) ↔
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)),
      (restrictedSumset A).card ≥ min (2 * A.card - 3) p := by
  sorry

end Erdos476

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

[Er65b] Erdős, P., *Some recent advances and current problems in number theory*.
Lectures on Modern Mathematics, Vol. III (1965), 196-244.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[dSHa94] da Silva, J.A.D. and Hamidoune, Y.O., *Cyclic spaces for Grassmann derivatives and
additive theory*, Bull. London Math. Soc. 26 (1994), 140-146.

[Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437, Problem C15.
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

/--
The restricted $r$-fold sumset of $A$: the set of all sums of exactly $r$ distinct elements of $A$.
-/
def restrictedSumset_r {p : ℕ} (A : Finset (ZMod p)) (r : ℕ) : Finset (ZMod p) :=
  A.powersetCard r |>.image (fun s => s.sum id)

/--
Erdős–Heilbronn generalized conjecture (Problem 476, variant):

Let $p$ be a prime, $A \subseteq \mathbb{F}_p$, and $r \geq 1$. The number of elements of
$\mathbb{F}_p$ that can be written as the sum of $r$ distinct elements of $A$ is at least
$\min(r|A| - r^2 + 1, p)$.

This generalization is mentioned by Erdős [Er65b] and appears as Problem C15 in Guy's
collection [Gu04]. Setting $r = 2$ recovers the original bound $\min(2|A| - 3, p)$.
-/
@[category research open, AMS 5 11]
theorem erdos_476_generalized :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)) (r : ℕ),
      (restrictedSumset_r A r).card ≥ min (r * A.card - r ^ 2 + 1) p := by
  sorry

end Erdos476

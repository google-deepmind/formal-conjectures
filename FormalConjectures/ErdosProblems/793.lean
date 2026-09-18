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
# Erdős Problem 793

*References:*
- [erdosproblems.com/793](https://www.erdosproblems.com/793)
- [Er38] Erdős, P., *On sequences of integers no one of which divides the product of two others
  and on some related problems*. Mitt. Forsch.-Inst. Math. Mech. Univ. Tomsk 2 (1938), 74-82.
- [Er69] Erdős, Paul, *Some applications of graph theory to number theory*. The Many Facets of
  Graph Theory (Proc. Conf., Western Mich. Univ., Kalamazoo, Mich., 1968) (1969), 77-82.
- [Er70b] Erdős, P., *Some applications of graph theory to number theory*. Proc. Second Chapel Hill
  Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel Hill, N.C.,
  1970) (1970), 136-145.
-/

open Filter Real
open scoped Topology

namespace Erdos793

/-- A finite set `A ⊆ ℕ` is *strongly 2-primitive* if `a ∤ b * c` whenever `a, b, c ∈ A` with
`a ≠ b` and `a ≠ c`. -/
def Strongly2Primitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c

/-- `F n` is the maximal size of a strongly 2-primitive subset of `{1, …, n}`. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter Strongly2Primitive).sup Finset.card

/--
Let $F(n)$ be the maximum possible size of a subset $A \subseteq \{1, \ldots, n\}$ such that
$a \nmid bc$ whenever $a, b, c \in A$ with $a \neq b$ and $a \neq c$. Is there a constant $c$ such
that
$$F(n) = \pi(n) + (c + o(1)) n^{2/3} (\log n)^{-2}?$$

A problem of Erdős [Er69, Er70b], who proved in [Er38] that
$F(n) = \pi(n) + O(n^{2/3} (\log n)^{-2})$. The answer is yes, with $c = 27/2$: this was proved by
GPT-5.6 Sol (prompted by Chojecki), refining the argument of [Er38]; see
`erdos_793.variants.constant`.
-/
@[category research solved, AMS 11]
theorem erdos_793 : answer(True) ↔
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦ ((F n : ℝ) - Nat.primeCounting n) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (log n) ^ 2)) atTop (𝓝 c) := by
  sorry

/--
The constant in Problem 793 is $c = 27/2$, i.e.
$$F(n) = \pi(n) + \left(\frac{27}{2} + o(1)\right) \frac{n^{2/3}}{(\log n)^2}.$$
Formalised by van Doorn and Aristotle, following the proof of GPT-5.6 Sol.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos793.lean#L25"]
theorem erdos_793.variants.constant :
    Tendsto (fun n : ℕ ↦ ((F n : ℝ) - Nat.primeCounting n) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (log n) ^ 2)) atTop (𝓝 (27 / 2)) := by
  sorry

end Erdos793

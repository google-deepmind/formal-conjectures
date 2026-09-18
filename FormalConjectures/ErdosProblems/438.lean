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
# Erdős Problem 438

*References:*
- [erdosproblems.com/438](https://www.erdosproblems.com/438)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Er80c] Erdős, Paul, *Nine little known problems in combinatorial number theory*. Normat (1980),
  155-164, 180.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [LOS83] Lagarias, J. C. and Odlyzko, A. M. and Shearer, J. B., *On the density of sequences of
  integers the sum of no two of which is a square. II. General sequences*. J. Combin. Theory Ser. A
  (1983), 123-139.
- [KLS02] Khalfalah, A. and Lodha, S. and Szemerédi, E., *Tight bound for the density of sequence
  of integers the sum of no two of which is a perfect square*. Discrete Math. (2002), 243-255.
-/

open Filter
open scoped Topology

namespace Erdos438

/-- A finite set of natural numbers is square-sum-free if the sum of any two of its elements
(possibly equal) is not a square. -/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

/-- All square-sum-free subsets of `{1, …, N}`. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SquareSumFree

/-- The largest size of a square-sum-free subset of `{1, …, N}`. -/
noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/--
How large can $A \subseteq \{1, \ldots, N\}$ be if $A + A$ contains no square numbers?

A problem of Erdős [Er80, Er80c, ErGr80]. Taking all integers $\equiv 1 \pmod 3$ gives
$|A| \ge N/3$, and Massias observed that all integers
$\equiv 1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30 \pmod{32}$ give $|A| \ge \frac{11}{32} N$.
Lagarias, Odlyzko and Shearer [LOS83] proved that $11/32$ is sharp for the modular version of the
problem, and Khalfalah, Lodha and Szemerédi [KLS02] proved that it is sharp in general: the
maximal such $A$ satisfies $|A| \le (\frac{11}{32} + o(1)) N$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos438.lean#L46"]
theorem erdos_438 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop (𝓝 ((11 : ℝ) / 32)) := by
  sorry

end Erdos438

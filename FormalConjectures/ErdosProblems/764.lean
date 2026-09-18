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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 764

*References:*
- [erdosproblems.com/764](https://www.erdosproblems.com/764)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Er70c] Erdős, P., *Some problems in additive number theory*. Amer. Math. Monthly (1970),
  619-621.
- [Va72] Vaughan, R. C., *On the addition of sequences of integers*. J. Number Theory (1972),
  1-16.
-/

@[expose] public section

open Filter Asymptotics AdditiveCombinatorics Set

namespace Erdos764

/-- The number of representations of `n` as an ordered sum of three elements of `A`,
$1_A\ast 1_A\ast 1_A(n)$. -/
noncomputable def tripleRep (A : Set ℕ) : ℕ → ℕ := 𝟙_A ∗ 𝟙_A ∗ 𝟙_A

/--
Let $A\subseteq \mathbb{N}$. Can there exist some constant $c>0$ such that
$$\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+O(1)?$$

The case of $1_A\ast 1_A(n)$ is the subject of [763](https://www.erdosproblems.com/763).

The answer is no, proved in a strong form by Vaughan [Va72], who showed that in fact
$$\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)$$
is impossible. Vaughan proves a more general result that applies to any $h$-fold convolution,
with different main terms permitted.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos764.lean#L3760"]
theorem erdos_764 : answer(False) ↔ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), tripleRep A n : ℝ) - c * N) =O[atTop]
      fun _ ↦ (1 : ℝ) := by
  sorry

/--
Vaughan [Va72] showed that
$\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)$ is
impossible.
-/
@[category research solved, AMS 11]
theorem erdos_764.variants.vaughan : ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), tripleRep A n : ℝ) - c * N) =o[atTop]
      fun N ↦ (N : ℝ) ^ (1 / 4 : ℝ) / √(Real.log N) := by
  sorry

end Erdos764

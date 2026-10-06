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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 763

*References:*
- [erdosproblems.com/763](https://www.erdosproblems.com/763)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Er70c] Erdős, P., *Some problems in additive number theory*. Amer. Math. Monthly (1970),
  619-621.
- [ErFu56] Erdős, P. and Fuchs, W. H. J., *On a problem of additive number theory*. J. London
  Math. Soc. (1956), 67-73.
- [MoVa90] Montgomery, H. L. and Vaughan, R. C., *On the Erdős-Fuchs theorems*. (1990), 331-338.
-/

@[expose] public section

open Filter Asymptotics AdditiveCombinatorics

namespace Erdos763

/--
Let $A\subseteq \mathbb{N}$. Can there exist some constant $c>0$ such that
$$\sum_{n\leq N} 1_A\ast 1_A(n) = cN+O(1)?$$

A conjecture of Erdős and Turán. Erdős and Fuchs [ErFu56] proved that the answer is no in a
strong form: in fact even
$$\sum_{n\leq N} 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)$$
is impossible. The error term here was improved to $o(N^{1/4})$ by Jurkat (unpublished) and
Montgomery and Vaughan [MoVa90].

See also [764](https://www.erdosproblems.com/764) for a generalisation to more summands.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos763.lean#L1464"]
theorem erdos_763 : answer(False) ↔ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), sumRep A n : ℝ) - c * N) =O[atTop]
      fun _ ↦ (1 : ℝ) := by
  sorry

/--
Erdős and Fuchs [ErFu56] proved that
$\sum_{n\leq N} 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)$ is impossible.
-/
@[category research solved, AMS 11]
theorem erdos_763.variants.erdos_fuchs : ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), sumRep A n : ℝ) - c * N) =o[atTop]
      fun N ↦ (N : ℝ) ^ (1 / 4 : ℝ) / √(Real.log N) := by
  sorry

/--
Jurkat (unpublished) and Montgomery and Vaughan [MoVa90] proved that even
$\sum_{n\leq N} 1_A\ast 1_A(n) = cN+o(N^{1/4})$ is impossible.
-/
@[category research solved, AMS 11]
theorem erdos_763.variants.montgomery_vaughan : ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), sumRep A n : ℝ) - c * N) =o[atTop]
      fun N ↦ (N : ℝ) ^ (1 / 4 : ℝ) := by
  sorry

end Erdos763

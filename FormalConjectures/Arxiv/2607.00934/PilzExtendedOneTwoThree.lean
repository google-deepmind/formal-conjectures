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
# Pilz's Extended 1-2-3 Conjecture

For finite sets $A, B$ of positive integers, let $A * B$ be the set of integers $m$ with an
odd number of ordered representations $m = ab$, $a \in A$, $b \in B$. Pilz's Extended 1-2-3
Conjecture asserts that $|A * [n]| \ge n$ for every finite nonempty $A$ and every $n \ge 1$,
where $[n] = \{1, \dots, n\}$; equivalently $|A \triangle 2A \triangle \cdots \triangle nA| \ge n$.
The case $A = [k]$ is the original 1-2-3 conjecture. (This is unrelated to the edge-weighting
1-2-3 conjecture of Karoński, Łuczak and Thomason.)

*References:*
* [Pi92] G. F. Pilz, *On polynomial near-ring codes*, Contrib. Gen. Algebra 8 (1992), 233--238.
* [HKP10] P.-Y. Huang, W.-F. Ke and G. F. Pilz, *The cardinality of some symmetric
  differences*, Proc. Amer. Math. Soc. 138 (2010), 787--797.
* [HP26] P. Holdridge and P. P. Pach, [On the Extended 1-2-3 Conjecture of
  Pilz](https://arxiv.org/abs/2607.00934) (2026). Proves the conjecture for all sufficiently
  large $n$, shows that the density $h(A) = \lim_n |A * [n]| / n$ exists, and proves
  $h(A) \ge 8/7$ outside two exceptional families; Remark 1.9 expects $4/3$.
* [Lean] [Lean 4 proofs of both statements below, with papers](
  https://github.com/odd-products/extended-1-2-3-conjecture-of-Pilz), archived at
  [doi:10.5281/zenodo.23568997](https://doi.org/10.5281/zenodo.23568997).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Arxiv.«2607.00934»

/-- The *odd product* $A * B$: the integers with an odd number of ordered representations
`m = a * b` with `a ∈ A` and `b ∈ B`. -/
def oddProduct (A B : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ B).image fun p => p.1 * p.2).filter fun m =>
    Odd ((A ×ˢ B).filter fun p => p.1 * p.2 = m).card

@[category test, AMS 5 11]
theorem oddProduct_one_two : oddProduct {1, 2} (Finset.Icc 1 2) = {1, 4} := by
  decide

set_option linter.style.formal_proof_palomar false in
/--
**Pilz's Extended 1-2-3 Conjecture.** For every finite nonempty set $A$ of positive integers
and every $n$, at least $n$ integers have an odd number of representations $aj$ with
$a \in A$ and $1 \le j \le n$.

Proved for all sufficiently large $n$ in [HP26]; a Lean 4 proof for every $n$ (as a special
case of a weighted statement over every field) is in [Lean], theorem `Pilz.pilz_conjecture`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/odd-products/extended-1-2-3-conjecture-of-Pilz/blob/b6ab2c22c0ba3658ef912e9db41ae91c7c8977f3/pilz/Pilz/Assembly.lean#L32"]
theorem pilz_extended_one_two_three (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty)
    (n : ℕ) : n ≤ (oddProduct A (Finset.Icc 1 n)).card := by
  sorry

/-- **The original 1-2-3 conjecture** ($A = [k]$), proved in [HKP10]. -/
@[category research solved, AMS 5 11]
theorem pilz_extended_one_two_three.variants.interval (k n : ℕ) (hk : 1 ≤ k) :
    n ≤ (oddProduct (Finset.Icc 1 k) (Finset.Icc 1 n)).card := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
**The optimal density bound** ([HP26], Remark 1.9). If $A$ is a finite nonempty set of positive
integers not of the form $\{a\}$ or $\{a, 2a\}$, then $|A * [n]| / n$ converges to a limit that
is at least $4/3$. The constant is attained by $A = \{1, 3\}$ [HP26].

A Lean 4 proof is in [Lean], theorem `PilzDensity.companion_theorem`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/odd-products/extended-1-2-3-conjecture-of-Pilz/blob/b6ab2c22c0ba3658ef912e9db41ae91c7c8977f3/pilz-density/Density/Certificate.lean#L10"]
theorem pilz_extended_one_two_three.variants.density_four_thirds (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty)
    (hexc : ¬ ∃ a, 0 < a ∧ (A = {a} ∨ A = {a, 2 * a})) :
    ∃ h : ℝ, 4 / 3 ≤ h ∧
      Tendsto (fun n : ℕ => ((oddProduct A (Finset.Icc 1 n)).card : ℝ) / n) atTop (𝓝 h) := by
  sorry

end Arxiv.«2607.00934»

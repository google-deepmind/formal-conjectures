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
# Erdős Problem 307

*References:*
- [erdosproblems.com/307](https://www.erdosproblems.com/307)
- Bonfioli, V., *On the equation n'' = n and a problem of Erdős and Barbeau on products of
  prime-reciprocal sums*,
  [doi:10.5281/zenodo.20684626](https://doi.org/10.5281/zenodo.20684626)
-/

@[expose] public section

namespace Erdos307

open scoped Finset

/--
Are there two finite set of primes $P$ and $Q$ such that

$$
1 = \left( \sum_{p \in P} \frac{1}{p} \right) \left( \sum_{q \in Q} \frac{1}{q} \right)
$$
?

Asked by Barbeau [Ba76].

[Ba76] Barbeau, E. J., _Computer challenge corner: Problem 477: A brute force program._
-/
@[category research open, question, AMS 11]
theorem erdos_307 : ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

/--
Instead of asking for sets of primes, ask only that all elements in the sets be relatively coprime.

Cambie has found several examples when this weakened version is true. For example,
$$
1=\left(1+\frac{1}{5}\right)\left(\frac{1}{2}+\frac{1}{3}\right)
$$
and
$$
1=\left(1+\frac{1}{41}\right)\left(\frac{1}{2}+\frac{1}{3}+\frac{1}{7}\right).
$$
-/
@[category textbook, AMS 5 11]
theorem erdos_307.variants.coprime : ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 < #P ∧ 1 < #Q ∧
    Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  simp only [Finset.mem_inter, not_and]
  use {1, 5}, {2, 3}
  norm_num +decide

/--
There are no examples known of the weakened coprime version if we insist that $1\not\in P\cup Q$.
-/
@[category research open, question, AMS 5 11]
theorem erdos_307.variants.coprime_one_notMem : ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧
    1 < #P ∧ 1 < #Q ∧ Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
A machine-checked **barrier** for Erdős 307 (Bonfioli, 2026): any solution with `Q` nonempty uses at
least 59 primes in total, and `(∏_{p ∈ P} p)² ≥ 4·10¹¹²` — i.e. `∏_{p ∈ P} p ≥ 2·10⁵⁶` (and, by
symmetry, the same for `∏ Q`); so no solution lies below a prime-product of `2.09·10⁵⁶`. The full
`sorry`-free proof is in the linked repository (`Closed.lean`): the left conjunct is `card_ge_59`,
the right is `erdos307_barrier_closed`. Both depend on `propext, Classical.choice, Quot.sound` and
nothing further: the evaluation of the first 59 primes is kernel-checked by `decide`, so no
`native_decide` enters this statement.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
"https://github.com/ElVec1o/erdos307/blob/76d242b024102f32d8411c714be4ad140a8b7c4b/lean/Erdos307/Closed.lean#L121"]
theorem erdos_307.barrier {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    59 ≤ #(P ∪ Q) ∧ (4 * 10 ^ 112 : ℚ) ≤ (∏ p ∈ P, (p : ℚ)) ^ 2 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
A stronger machine-checked **barrier** (Bonfioli, 2026), closing the 59-prime level: any solution of
Erdős 307 in fact uses at least `60` primes in total. The full `sorry`-free proof is `erdos307_sixty`
in the linked repository (`Sixty.lean` at tag `v1.1.1`); its only non-logical input is a `native_decide`
depth-first search establishing that no admissible 59-prime support survives the Pythagorean
`plus`-value square test, with axioms `propext, Classical.choice, Quot.sound` together with that
`native_decide`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
"https://github.com/ElVec1o/erdos307/blob/080164a8db2eeb20f65c362894ec93f12448609a/lean/Erdos307/Sixty.lean#L367"]
theorem erdos_307.barrier_sixty {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    60 ≤ #(P ∪ Q) := by
  sorry

/--
A further strengthening of the barrier (Bonfioli, 2026): any solution of Erdős 307 uses at least
`61` primes in total, i.e. no solution has exactly `60`. A `60`-prime support of mass above `2` is
either a one-new-prime extension of one of the admissible `59`-prime bases or lies in the "pair
sector"; both are shown empty by finite computation (Proposition `prop:level60closed` of the paper).

**This statement is not fully machine-checked, and no `formal_proof` attribute is given.** In the
linked repository (release v1.76.2, doi:10.5281/zenodo.23447903) the pair sector, the kill stage and
the tail sieve are checked in Lean in a separate tier that uses `native_decide` (39 compiled
evaluations). The kill stage checks a list of `3698` surviving bases (called pools in the Lean source)
together with the divisor kills; the factoring search that produced that list is not in Lean.
`erdos307_sixtyone_of_stageA` (`Computational/QSieveFinal.lean`) derives the barrier `61` from one
remaining named statement, `StageAList`: no listed pool carries a cycle in the lower window
(`α² · 2^40 ≤ D`). An independent program re-ran that lower-window enumeration on the same `3698`
bases with no hit, but it is not in Lean. The earlier barriers above do carry a `formal_proof`.
-/
@[category research solved, AMS 11]
theorem erdos_307.barrier_sixtyone {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    61 ≤ #(P ∪ Q) := by
  sorry

end Erdos307

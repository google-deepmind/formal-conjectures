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
# Erdős Problem 475

Let $p$ be a prime. Is it true that every subset $A \subseteq \mathbb{F}_p \setminus \{0\}$ admits
a sequencing $a_1, \ldots, a_t$ such that all partial sums $\sum_{k=1}^{m} a_k$ are distinct?

## References

[ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique (1980).

[CoPe20] Costa, S. and Pellegrini, M.A., _Some new results about a conjecture by Brian
Alspach_. Archiv der Mathematik (Basel) (2020), 479–488.

[HOS19] Hicks, J., Ollis, M.A., and Schmitt, J.R., _Distinct partial sums in cyclic groups:
polynomial method and constructive approaches_. Journal of Combinatorial Designs (2019),
369–385.

[Kr24] Kravitz, N., _Rearranging small sets for distinct partial sums_. arXiv:2407.01835 (2024).

[BeKr24] Bedert, B. and Kravitz, N., _Graham's rearrangement conjecture beyond the
rectification barrier_. arXiv:2409.07403 (2024).

[MuPo25] Müyesser, A. and Pokrovskiy, A., _A random Hall–Paige conjecture_.
arXiv:2204.09666 (2025).

[BBKMM25] Bedert, B., Bucić, M., Kravitz, N., Montgomery, R., and Müyesser, A.,
_On Graham's rearrangement conjecture over ℤ₂ⁿ_. arXiv:2508.18254 (2025).

[PhSa26] Pham, H.T. and Sauermann, L., _On Graham's rearrangement conjecture_.
arXiv:2602.15797 (2026).

[CoDe26] Costa, S. and Della Fiore, S., _New bounds for (weak) sequenceability in ℤₖ_.
arXiv:2602.19989 (2026).

*Reference:* [erdosproblems.com/475](https://www.erdosproblems.com/475)
-/

open Finset BigOperators

namespace Erdos475

/--
The partial sum of a sequence $f$ at index $m$: the sum $f(0) + f(1) + \cdots + f(m)$.
-/
noncomputable def partialSum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin n → α) (m : Fin n) : α :=
  (univ.filter (fun i : Fin n => i ≤ m)).sum f

/--
Erdős-Graham Conjecture on sequenceable sets in $\mathbb{F}_p$ (Problem 475):
Let $p$ be a prime. Given any finite set $A \subseteq \mathbb{F}_p \setminus \{0\}$, there always
exists a rearrangement $A = \{a_1, \ldots, a_t\}$ such that all partial sums
$\sum_{1 \le k \le m} a_k$ are distinct, for all $1 \le m \le t$.

Such an ordering is called a "valid ordering" or "sequencing" of $A$.
Graham proved the case $t = p - 1$ [ErGr80].

The conjecture has been resolved for all sufficiently large primes via four complementary
results: small sets [Kr24] [CoDe26], medium sets [PhSa26], large sets [BBKMM25] [BeKr24],
and very large sets [MuPo25]. Earlier, the conjecture was verified for $t \leq 12$ [CoPe20]
and for $p - 3 \leq t \leq p - 1$ [HOS19].
-/
@[category research open, AMS 5 11]
theorem erdos_475 (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p))
    (hA : ∀ a ∈ A, a ≠ 0) :
    ∃ f : Fin A.card → ZMod p,
      (∀ i, f i ∈ A) ∧
      Function.Injective f ∧
      Function.Injective (partialSum f) := by
  sorry

end Erdos475

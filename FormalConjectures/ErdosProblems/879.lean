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
# Erdős Problem 879

*References:*
- [erdosproblems.com/879](https://www.erdosproblems.com/879)
- [P. Erdős, On two unconventional number theoretic functions and on some related problems]
  (https://www.renyi.hu/~p_erdos/1984-16.pdf)
- [OEIS A186736](https://oeis.org/A186736)
-/

open scoped BigOperators
open Filter Asymptotics

namespace Erdos879

/-- An admissible subset of $\{1, \ldots, n\}$: distinct members are pairwise coprime. -/
def IsAdmissible (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 1 n ∧ (S : Set ℕ).Pairwise Nat.Coprime

/-- The maximum of $\sum_{a \in S} a$ over all admissible subsets $S$ of $\{1, \ldots, n\}$. -/
noncomputable def G (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter (IsAdmissible n)).sup (fun S ↦ S.sum id)

/--
The comparison function
$$H(n) = \sum_{p < n} p + n \pi(\sqrt{n}),$$
where $p$ runs over primes. Since $\pi(\sqrt{n}) = \pi(\lfloor \sqrt{n} \rfloor)$, the second
term uses `Nat.primeCounting (Nat.sqrt n)`.
-/
def H (n : ℕ) : ℕ :=
  (∑ p ∈ (Finset.range n).filter Nat.Prime, p) +
    n * Nat.primeCounting (Nat.sqrt n)

/-- An admissible set whose sum is maximal among all admissible sets for $n$. -/
def IsOptimal (n : ℕ) (S : Finset ℕ) : Prop :=
  IsAdmissible n S ∧ ∀ T : Finset ℕ, IsAdmissible n T → T.sum id ≤ S.sum id

/--
Call a set $S \subseteq \{1, \ldots, n\}$ admissible if $(a,b)=1$ for all $a \neq b \in S$.
Let
$$G(n) = \max_{S \subseteq \{1, \ldots, n\}} \sum_{a \in S} a$$
and
$$H(n)=\sum_{p<n}p + n\pi(n^{1/2}).$$
Is it true that
$$G(n) > H(n)-n^{1+o(1)}?$$
-/
@[category research open, AMS 11]
theorem erdos_879.parts.i :
    answer(sorry) ↔
      ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ n : ℕ in atTop,
          (G n : ℝ) > (H n : ℝ) - (n : ℝ) ^ (1 + o n) := by
  sorry

/--
Is it true that, for every $k \geq 2$, if $n$ is sufficiently large then the admissible set which
maximises $G(n)$ contains at least one integer with at least $k$ prime factors?

Prime factors are counted without multiplicity, i.e. by `a.primeFactors.card`.
The linked Lean proof gives a negative answer, already for $k=3$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-879-lean/blob/e5356c5579acdfbe488acf72514a19cc332da501/lean/Erdos879Final.lean#L233-L243"]
theorem erdos_879.parts.ii :
    answer(False) ↔
      ∀ k : ℕ, 2 ≤ k →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ S : Finset ℕ, IsOptimal n S ∧ ∃ a ∈ S, k ≤ a.primeFactors.card := by
  sorry

end Erdos879

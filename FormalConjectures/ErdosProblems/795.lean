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
# Erdős Problem 795

*References:*
- [erdosproblems.com/795](https://www.erdosproblems.com/795)
- [Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189.
- [Er69] Erdős, Paul, _Some applications of graph theory to number theory_. The Many Facets of
  Graph Theory (Proc. Conf., Western Mich. Univ., Kalamazoo, Mich., 1968) (1969), 77-82.
- [Er70b] Erdős, P., _Some applications of graph theory to number theory_. Proc. Second Chapel
  Hill Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel
  Hill, N.C., 1970) (1970), 136-145.
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [Er66] Erdős, Pál, _Remarks on number theory. V. Extremal problems in number theory. II_. Mat.
  Lapok (1966), 135--155.
- [Ra25] R. Raghavan, _Sharp Bounds for Sets with Distinct Subset Products_. arXiv:2501.02695
  (2025).
-/

@[expose] public section

open Filter Real

namespace Erdos795

/-- `A` has distinct subset products: the products $\prod_{n\in S}n$ are distinct for all
$S\subseteq A$. -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  Set.InjOn (fun S : Finset ℕ ↦ ∏ n ∈ S, n) (A.powerset : Set (Finset ℕ))

/-- `g n` is the maximal size of $A\subseteq \{1,\ldots,n\}$ with distinct subset products. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 n, HasDistinctSubsetProducts A ∧ A.card = k}

/--
Let $g(n)$ be the maximal size of $A\subseteq \{1,\ldots,n\}$ such that the products
$\prod_{n\in S}n$ are distinct for all $S\subseteq A$. Is it true that
$$g(n) \leq \pi(n)+\pi(n^{1/2})+o\left(\frac{n^{1/2}}{\log n}\right)?$$

The answer is yes, proved by Raghavan [Ra25], who proved that
$g(n) \leq \pi(n)+\pi(n^{1/2})+O(n^{5/12+o(1)})$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos795.lean#L6651"]
theorem erdos_795 : answer(True) ↔
    ∃ e : ℕ → ℝ, (e =o[atTop] fun n : ℕ ↦ √n / log n) ∧
      ∀ n, (g n : ℝ) ≤ Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) + e n := by
  sorry

/-- Erdős proved [Er66] that $g(n) \leq \pi(n)+O\left(\frac{n^{1/2}}{\log n}\right)$. -/
@[category research solved, AMS 11]
theorem erdos_795.variants.erdos_upper_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ Nat.primeCounting n + C * (√n / log n) := by
  sorry

/-- Raghavan [Ra25] proved that $g(n) \leq \pi(n)+\pi(n^{1/2})+O(n^{5/12+o(1)})$. -/
@[category research solved, AMS 11]
theorem erdos_795.variants.raghavan_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) +
        C * (n : ℝ) ^ (5 / 12 + ε : ℝ) := by
  sorry

/-- Raghavan [Ra25] also proved that $g(n) \geq \pi(n)+\pi(n^{1/2})+\pi(n^{1/3})/3-O(1)$. -/
@[category research solved, AMS 11]
theorem erdos_795.variants.raghavan_lower_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) + Nat.primeCounting (Nat.sqrt n) +
        (Nat.primeCounting (Nat.nthRoot 3 n) : ℝ) / 3 - C ≤ g n := by
  sorry

/-- Taking $A$ to be all primes and squares of primes gives
$g(n) \geq \pi(n)+\pi(n^{1/2})$. -/
@[category textbook, AMS 11]
theorem erdos_795.variants.primes_and_squares (n : ℕ) :
    Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) ≤ g n := by
  sorry

end Erdos795

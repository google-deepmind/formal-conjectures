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
# Erdős Problem 874

*References:*
- [erdosproblems.com/874](https://www.erdosproblems.com/874)
- [Er62c] Erdős, Pál, _Some remarks on number theory. III_. Mat. Lapok (1962), 28--38.
- [Er98] Erdős, Paul, _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [St66] Straus, E. G., _On a problem in combinatorial number theory_. J. Math. Sci. (1966),
  77--80.
- [ENS91] Erdős, P. and Nicolas, J.-L. and Sárközy, A., _Sommes de sous-ensembles_. Sém. Théor.
  Nombres Bordeaux (2) (1991), 55--72.
- [DeFr99] Deshouillers, Jean-Marc and Freiman, Gregory A., _On an additive problem of Erdős
  and Straus. II_. Astérisque (1999), xii, 141--148.
-/

@[expose] public section

open Filter Finset

namespace Erdos874

/-- $S_r(A) = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}$, the sums of `r` distinct elements
of `A`. -/
def sumsOf (r : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.powersetCard r).image fun B ↦ ∑ a ∈ B, a

/-- `A` is *admissible* (Straus) if the sets $S_r(A)$ are disjoint for distinct $r\geq 1$. -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s → r ≠ s → Disjoint (sumsOf r A) (sumsOf s A)

/-- `k N` is the size of the largest admissible $A\subseteq \{1,\ldots,N\}$. -/
noncomputable def k (N : ℕ) : ℕ :=
  sSup {m | ∃ A ⊆ Finset.Icc 1 N, IsAdmissible A ∧ A.card = m}

/--
Let $k(N)$ denote the size of the largest set $A\subseteq \{1,\ldots,N\}$ such that the sets
$$S_r = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}$$
are disjoint for distinct $r\geq 1$. Estimate $k(N)$ - in particular, is it true that
$k(N)\sim 2N^{1/2}$?

The answer is yes: the conjecture was proved (for all large $N$) by Deshouillers and Freiman
[DeFr99]. Straus [St66] proved $\limsup k(N)/N^{1/2}\leq 4/\sqrt{3}$ and
$\liminf k(N)/N^{1/2}\geq 2$; Erdős, Nicolas, and Sárközy [ENS91] improved the upper bound to
$(143/27)^{1/2}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos874.lean#L109"]
theorem erdos_874 : answer(True) ↔
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / √N) atTop (nhds 2) := by
  sorry

/-- Straus [St66] proved that $A=(N-k,N]\cap \mathbb{N}$ is admissible for $k=2m-1$ if
$N\in [m^2,m^2+m)$ and for $k=2m$ if $N\in [m^2+m,(m+1)^2)$. -/
@[category research solved, AMS 11]
theorem erdos_874.variants.straus (m N : ℕ) (hm : 1 ≤ m) :
    (m ^ 2 ≤ N → N < m ^ 2 + m → IsAdmissible (Finset.Ioc (N - (2 * m - 1)) N)) ∧
    (m ^ 2 + m ≤ N → N < (m + 1) ^ 2 → IsAdmissible (Finset.Ioc (N - 2 * m) N)) := by
  sorry

end Erdos874

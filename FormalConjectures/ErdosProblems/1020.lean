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
# Erdős Problem 1020

Conjecture on the maximum number of edges in an $r$-uniform hypergraph on $n$ vertices
containing no matching of size $k$ (the Erdős Matching Conjecture).

*Reference:* [erdosproblems.com/1020](https://www.erdosproblems.com/1020)

[Er65d] Erdős, P., *A problem on independent r-tuples*, Ann. Univ. Sci. Budapest. Eötvös Sect.
Math. 8 (1965), 93–95.

[Er71] Erdős, P., *Topics in combinatorial analysis*, Proc. Second Louisiana Conf. on
Combinatorics, Graph Theory and Computing (1971), 2–20.
-/

open Finset

namespace Erdos1020

/-- An $r$-uniform hypergraph on vertex set `Fin n`: every edge has exactly $r$ vertices. -/
def IsRUniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A matching of size $k$ in a hypergraph: $k$ pairwise vertex-disjoint edges. -/
def HasMatching {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- `maxEdgesNoMatching n r k` is the maximum number of edges in an $r$-uniform hypergraph
on $n$ vertices that contains no matching of size $k$. -/
noncomputable def maxEdgesNoMatching (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)),
    IsRUniform H r ∧ ¬HasMatching H k ∧ H.card = m}

/--
Erdős Problem 1020 (Erdős Matching Conjecture) [Er65d, Er71, p.103]:

For all $r \geq 3$, the maximum number of edges in an $r$-uniform hypergraph on $n$ vertices
containing no matching of size $k$ equals
$$
  \max\left(\binom{rk-1}{r},\; \binom{n}{r} - \binom{n-k+1}{r}\right).
$$
-/
@[category research open, AMS 5]
theorem erdos_1020 (n r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1) :
    maxEdgesNoMatching n r k =
      max (Nat.choose (r * k - 1) r) (Nat.choose n r - Nat.choose (n - k + 1) r) := by
  sorry

end Erdos1020

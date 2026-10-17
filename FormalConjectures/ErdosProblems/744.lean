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
# Erdős Problem 744

*References:*
- [erdosproblems.com/744](https://www.erdosproblems.com/744)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E., *On almost bipartite large chromatic
  graphs*. Theory and practice of combinatorics (1982), 117-123.
- [Ga68] T. Gallai, *On covering of graphs*. Theory of Graphs, Proc. Coll. Tihany, Hungary
  (1968), 231-236.
- [RoTu85] Rödl, Vojtěch and Tuza, Zsolt, *On color critical graphs*. J. Combin. Theory Ser. B
  (1985), 204-213.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos744

variable {V : Type*}

/--
A graph `G` is `k`-critical if it has chromatic number `k` and every proper subgraph has
chromatic number `< k`.
-/
def IsCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < k

/-- The least number of edges whose deletion makes `G` bipartite. -/
noncomputable def bipartizationNumber (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ E ⊆ G.edgeSet, E.ncard = m ∧ (G.deleteEdges E).IsBipartite}

/--
`f k n` is the minimal `m` such that there exists a `k`-critical graph on `n` vertices which can
be made bipartite by deleting `m` edges.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), IsCritical G k ∧ bipartizationNumber G = m}

/--
Let $k$ be a large fixed constant. Let $f_k(n)$ be the minimal $m$ such that there exists a graph
$G$ on $n$ vertices with chromatic number $k$, such that every proper subgraph has chromatic number
$<k$, and $G$ can be made bipartite by deleting $m$ edges. Is it true that $f_k(n)\to \infty$ as
$n\to \infty$? In particular, is it true that $f_4(n) \gg \log n$?

A problem of Erdős, Hajnal, and Szemerédi [EHS82]. Odd cycles show that $f_3(n)=1$, but they
expected $f_4(n)\to \infty$. Gallai [Ga68] gave a construction which shows $f_4(n) \ll n^{1/2}$,
and Lovász extended this to show $f_k(n) \ll n^{1-\frac{1}{k-2}}$.

This conjecture was disproved by Rödl and Tuza [RoTu85], who proved that in fact
$f_k(n)=\binom{k-1}{2}$ (for all sufficiently large $n$).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos744.lean#L1999"]
theorem erdos_744 : answer(False) ↔ ∀ k : ℕ, 4 ≤ k → Tendsto (f k) atTop atTop := by
  sorry

/-- Is it true that $f_4(n) \gg \log n$? No: $f_4(n) = 3$ for all large $n$ [RoTu85]. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos744.lean#L1999"]
theorem erdos_744.variants.four : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ f 4 n := by
  sorry

/-- Rödl and Tuza [RoTu85] proved that $f_k(n)=\binom{k-1}{2}$ for all sufficiently large $n$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos744.lean#L1999"]
theorem erdos_744.variants.rodl_tuza : ∀ k : ℕ, 4 ≤ k →
    ∀ᶠ n : ℕ in atTop, f k n = (k - 1).choose 2 := by
  sorry

/-- Odd cycles show that $f_3(n)=1$ (for odd $n$, the only $3$-critical graphs being odd cycles). -/
@[category research solved, AMS 5]
theorem erdos_744.variants.three : ∀ n : ℕ, 3 ≤ n → Odd n → f 3 n = 1 := by
  sorry

end Erdos744

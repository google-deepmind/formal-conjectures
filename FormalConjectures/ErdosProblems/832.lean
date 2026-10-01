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
public import FormalConjectures.ErdosProblems.«833»

/-!
# Erdős Problem 832

*References:*
- [erdosproblems.com/832](https://www.erdosproblems.com/832)
- [Er74d] Erdős, Paul, *Unsolved Problems*. (1974), 278-297.
- [Al85] Alon, Noga, *Hypergraphs with high chromatic number*. Graphs Combin. (1985), 387-389.
- [AkSh16] Akolzin, Ilia and Shabanov, Dmitry, *Colorings of hypergraphs with large number of
  colors*. Discrete Math. (2016), 3020-3031.
- [ChPe20] Cherkashin, Danila and Petrov, Fedor, *Regular behavior of the maximal hypergraph
  chromatic number*. SIAM J. Discrete Math. (2020), 1326-1333.
-/

@[expose] public section

open Filter Asymptotics Erdos833

namespace Erdos832

/--
Let $r\geq 3$ and $k$ be sufficiently large in terms of $r$. Is it true that every $r$-uniform
hypergraph with chromatic number $k$ has at least
$$\binom{(r-1)(k-1)+1}{r}$$
edges, with equality only for the complete graph on $(r-1)(k-1)+1$ vertices?

When $r=2$ it is a classical fact that chromatic number $k$ implies at least $\binom{k}{2}$ edges.
Erdős asked for $k$ to be large in this conjecture since he knew it to be false for $r=k=3$, as
witnessed by the Steiner triples with $7$ vertices and $7$ edges.

This was disproved by Alon [Al85], who proved, for example, that there exists some absolute
constant $C>0$ such that if $r\geq C$ and $k\geq Cr$ then there exists an $r$-uniform hypergraph
with chromatic number $\geq k$ with at most $(7/8)^r\binom{(r-1)(k-1)+1}{r}$ many edges.

In general, Alon gave an upper bound for the minimal number of edges using Turán numbers. Using
known bounds for Turán numbers then suffices to disprove this conjecture for all $r\geq 4$. The
validity of this conjecture for $r=3$ remains open.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos832.lean#L896"]
theorem erdos_832 : answer(False) ↔ ∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ (V : Type) [Fintype V] (H : Finset (Finset V)), (∀ e ∈ H, e.card = r) →
      HasChromaticNumber H k → ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
        (H.card = ((r - 1) * (k - 1) + 1).choose r →
          ∃ S : Finset V, S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r) := by
  sorry

/-- The validity of this conjecture for $r=3$ remains open. -/
@[category research open, AMS 5]
theorem erdos_832.variants.three : answer(sorry) ↔ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ (V : Type) [Fintype V] (H : Finset (Finset V)), (∀ e ∈ H, e.card = 3) →
      HasChromaticNumber H k → (2 * (k - 1) + 1).choose 3 ≤ H.card ∧
        (H.card = (2 * (k - 1) + 1).choose 3 →
          ∃ S : Finset V, S.card = 2 * (k - 1) + 1 ∧ H = S.powersetCard 3) := by
  sorry

/--
Alon [Al85] proved that there exists some absolute constant $C>0$ such that if $r\geq C$ and
$k\geq Cr$ then there exists an $r$-uniform hypergraph with chromatic number $\geq k$ with at most
$(7/8)^r\binom{(r-1)(k-1)+1}{r}$ many edges.
-/
@[category research solved, AMS 5]
theorem erdos_832.variants.alon : ∃ C : ℕ, 0 < C ∧ ∀ r k : ℕ, C ≤ r → C * r ≤ k →
    ∃ (V : Type) (_ : Fintype V) (H : Finset (Finset V)), (∀ e ∈ H, e.card = r) ∧
      (¬ ∃ c : V → Fin (k - 1), IsProperColoring H c) ∧
        (H.card : ℝ) ≤ (7 / 8) ^ r * ((r - 1) * (k - 1) + 1).choose r := by
  sorry

/--
`m r k` is the minimal number of edges of any $r$-uniform hypergraph with chromatic number $>k$.
-/
noncomputable def m (r k : ℕ) : ℕ :=
  sInf {n | ∃ (V : Type) (_ : Fintype V) (H : Finset (Finset V)), (∀ e ∈ H, e.card = r) ∧
    (¬ ∃ c : V → Fin k, IsProperColoring H c) ∧ H.card = n}

/--
Akolzin and Shabanov [AkSh16] have proved
$$\frac{r}{\log r}k^r \ll m(r,k) \ll (r^3\log r) k^r,$$
where the implied constants are absolute.
-/
@[category research solved, AMS 5]
theorem erdos_832.variants.akolzin_shabanov : ∃ c C : ℝ, 0 < c ∧
    ∀ r k : ℕ, 2 ≤ r → 2 ≤ k → c * (r / Real.log r) * (k : ℝ) ^ r ≤ m r k ∧
      (m r k : ℝ) ≤ C * (r ^ 3 * Real.log r) * (k : ℝ) ^ r := by
  sorry

/--
Cherkashin and Petrov [ChPe20] have proved that, for fixed $r$, $m(r,k)/k^r$ converges to some
limit as $k\to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_832.variants.cherkashin_petrov : ∀ r : ℕ, 2 ≤ r →
    ∃ L : ℝ, Tendsto (fun k : ℕ ↦ (m r k : ℝ) / (k : ℝ) ^ r) atTop (nhds L) := by
  sorry

end Erdos832

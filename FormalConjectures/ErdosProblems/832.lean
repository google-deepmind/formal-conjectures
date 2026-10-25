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
# Erdős Problem 832

*References:*
- [erdosproblems.com/832](https://www.erdosproblems.com/832)
- [AkSh16] Akolzin, Ilia and Shabanov, Dmitry, Colorings of hypergraphs with large number of colors.
  Discrete Math. (2016), 3020--3031.
- [Al85] Alon, Noga, Hypergraphs with high chromatic number. Graphs Combin. (1985), 387--389.
- [ChPe20] Cherkashin, Danila and Petrov, Fedor, Regular behavior of the maximal hypergraph
  chromatic number. SIAM J. Discrete Math. (2020), 1326--1333.
-/

@[expose] public section

namespace Erdos832

open Filter Asymptotics

/--
Let $r\geq 3$ and $k$ be sufficiently large in terms of $r$. Is it true that every $r$-uniform
hypergraph with chromatic number $k$ has at least
$$\binom{(r-1)(k-1)+1}{r}$$
edges, with equality only for the complete graph on $(r-1)(k-1)+1$ vertices?

This was disproved by Alon [Al85]. The validity of this conjecture for $r=3$ remains open.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos832.lean#L896"]
theorem erdos_832 :
    ¬ ∀ r : ℕ, 3 ≤ r → ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber k →
      ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
      (H.card = ((r - 1) * (k - 1) + 1).choose r →
        ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r) := by
  sorry

/-- The case of three-uniform hypergraphs remains open. -/
@[category research open, question, AMS 5]
theorem erdos_832.variants.three : ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform 3 → H.HasHypergraphChromaticNumber k →
      (2 * (k - 1) + 1).choose 3 ≤ H.card ∧
      (H.card = (2 * (k - 1) + 1).choose 3 →
        ∃ S : Finset (Fin n), S.card = 2 * (k - 1) + 1 ∧ H = S.powersetCard 3) := by
  sorry

/-- Alon gives counterexamples with at most $(7/8)^r$ times the proposed number of edges. -/
@[category research solved, AMS 5]
theorem erdos_832.variants.alon : ∃ C : ℕ, 0 < C ∧ ∀ r k : ℕ, C ≤ r → C * r ≤ k →
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r ∧
      ¬ H.HypergraphColorable (k - 1) ∧
      (H.card : ℝ) ≤ (7 / 8) ^ r * ((r - 1) * (k - 1) + 1).choose r := by
  sorry

/-- The minimum number of edges of an `r`-uniform hypergraph not colorable with `k` colors. -/
noncomputable def m (r k : ℕ) : ℕ :=
  sInf {e | ∃ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform r ∧
    ¬ H.HypergraphColorable k ∧ H.card = e}

/-- Akolzin and Shabanov prove $r k^r / \log r \ll m(r,k) \ll r^3 (\log r) k^r$. -/
@[category research solved, AMS 5]
theorem erdos_832.variants.akolzin_shabanov : ∃ c C : ℝ, 0 < c ∧
    ∀ r k : ℕ, 2 ≤ r → 2 ≤ k → c * (r / Real.log r) * (k : ℝ) ^ r ≤ m r k ∧
      (m r k : ℝ) ≤ C * (r ^ 3 * Real.log r) * (k : ℝ) ^ r := by
  sorry

/-- For fixed `r`, Cherkashin and Petrov prove convergence of $m(r,k)/k^r$. -/
@[category research solved, AMS 5]
theorem erdos_832.variants.cherkashin_petrov : ∀ r : ℕ, 2 ≤ r →
    ∃ L : ℝ, Tendsto (fun k : ℕ ↦ (m r k : ℝ) / (k : ℝ) ^ r) atTop (nhds L) := by
  sorry

end Erdos832

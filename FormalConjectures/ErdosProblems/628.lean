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
# Erdős Problem 628

*References:*
- [erdosproblems.com/628](https://www.erdosproblems.com/628)
- [BKPS09] Balogh, József and Kostochka, Alexandr V. and Prince, Noah and Stiebitz, Michael,
  *The Erdős-Lovász Tihany conjecture for quasi-line graphs*. Discrete Math. (2009), 3985-3991.
- [BrJu69] Brown, W. G. and Jung, H. A., *On odd circuits in chromatic graphs*. Acta Math. Acad.
  Sci. Hungar. (1969), 129-134.
- [Er68b] Erdős, P., *Problem 2*. Theory of Graphs (1968), 361.
- [So22] Song, Zi-Xia, *A survey on the Erdős-Lovász Tihany conjecture*. Adv. Math. (China)
  (2022), 259--274.
-/

namespace Erdos628

open SimpleGraph

/--
Let $G$ be a graph with chromatic number $k$ containing no $K_k$. If $a,b\geq 2$ and $a+b=k+1$
then must there exist two disjoint subgraphs of $G$ with chromatic numbers $\geq a$ and $\geq b$
respectively?
-/
@[category research open, AMS 5]
theorem erdos_628 (V : Type*) [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hG_chrom : G.chromaticNumber = (k : ℕ∞))
    (hG_clique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  sorry

/- ## Variants and partial results -/

/--
Erdős originally asked about $a=b=3$ which was proved by Brown and Jung.
-/
@[category research solved, AMS 5]
theorem erdos_628.variants.k_5_a_3_b_3 (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG_chrom : G.chromaticNumber = (5 : ℕ∞))
    (hG_clique : G.CliqueFree 5) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (3 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (3 : ℕ∞) := by
  sorry

/--
Balogh, Kostochka, Prince, and Stiebitz proved the conjecture for quasi-line graphs.
-/
@[category research solved, AMS 5]
theorem erdos_628.variants.quasi_line (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG_quasi : IsQuasiLineGraph G)
    (k : ℕ)
    (hG_chrom : G.chromaticNumber = (k : ℕ∞))
    (hG_clique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  sorry

/--
Balogh, Kostochka, Prince, and Stiebitz proved the conjecture for graphs with independence number 2.
-/
@[category research solved, AMS 5]
theorem erdos_628.variants.independence_number_2 (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG_indep : G.indepNum = 2)
    (k : ℕ)
    (hG_chrom : G.chromaticNumber = (k : ℕ∞))
    (hG_clique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  sorry

end Erdos628

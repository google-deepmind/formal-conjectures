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
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Erdős Problem 666

*Reference:* [erdosproblems.com/666](https://www.erdosproblems.com/666)

Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices
and $n \cdot 2^{n-1}$ edges). Is it true that, for every $\epsilon > 0$, if $n$ is
sufficiently large, every subgraph of $Q_n$ with $\geq \epsilon \cdot n \cdot 2^{n-1}$
many edges contains a $C_6$?

The answer is no: Chung [Ch92] and Brouwer, Dejter, and Thomassen [BDT93] constructed
an edge-partition of $Q_n$ into four subgraphs, each containing no $C_6$.

[Er91] Erdős, P., *Some of my favourite problems in various branches of combinatorics*.
Matematiche (Catania) 47 (1992), no. 2, 231-240 (1993).

[Er92b] Erdős, P., *Some of my old and new problems in elementary number theory and
geometry*. Proceedings of the Fifth Canadian Number Theory Association Conference (1992).

[Er97f] Erdős, P., *Some recent problems and results in graph theory*. Discrete Math.
164 (1997), no. 1-3, 81-85.

[Ch92] Chung, F., *Subgraphs of a hypercube containing no small even cycles*. J. Graph
Theory 16 (1992), no. 3, 273-286.

[BDT93] Brouwer, A. E., Dejter, I. J., and Thomassen, C., *Highly symmetric subgraphs
of hypercubes*. J. Algebraic Combin. 2 (1993), no. 1, 25-29.
-/

open SimpleGraph Finset

namespace Erdos666

/-- The $n$-dimensional hypercube graph $Q_n$. Vertices are functions
$\operatorname{Fin} n \to \operatorname{Bool}$, and two vertices are adjacent iff they
differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless v := fun ⟨hne, _⟩ => hne rfl

/--
Erdős Problem 666 (disproved) [Er91][Er92b][Er97f]:

Is it true that, for every $\epsilon > 0$, if $n$ is sufficiently large, every subgraph of $Q_n$
with $\geq \epsilon \cdot n \cdot 2^{n-1}$ edges contains a $C_6$?

The answer is no. Chung [Ch92] and Brouwer, Dejter, and Thomassen [BDT93] constructed
an edge-partition of $Q_n$ into four subgraphs, each containing no $C_6$.
-/
@[category research solved, AMS 5]
theorem erdos_666 : answer(False) ↔
    (∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ H : SimpleGraph (Fin n → Bool),
        (∀ u v, H.Adj u v → (hypercubeGraph n).Adj u v) →
        (↑(H.edgeFinset.card) : ℝ) ≥ ε * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) →
        ∃ f : Fin 6 → (Fin n → Bool), Function.Injective f ∧
          ∀ i j, (SimpleGraph.cycleGraph 6).Adj i j → H.Adj (f i) (f j)) := by
  sorry

end Erdos666

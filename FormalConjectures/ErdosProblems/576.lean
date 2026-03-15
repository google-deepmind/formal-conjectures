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
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Erdős Problem 576

Erdős conjectured that the Turán number of the 3-dimensional hypercube graph $Q_3$
satisfies $\mathrm{ex}(n; Q_3) \asymp n^{8/5}$.

*Reference:* [erdosproblems.com/576](https://www.erdosproblems.com/576)

References:
- [Er64c] Erdős, P. (1964).
- [Er74c] Erdős, P., _Extremal problems on graphs and hypergraphs_. (1974), 75-84.
- [Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. (1975).
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_. Combinatorica (1981), 25-42.
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_. Quaestiones Mathematicae (1993), 333-350.
- [ErSi70] Erdős, P., Simonovits, M., _Some extremal problems in graph theory_. Combinatorial Theory and Its Applications, I-III (1970), 377-390.
- [JaSu22] Janzer, O., Sudakov, B., _On the Turán number of the hypercube_. arXiv:2211.02015 (2024).
- [SuTo22] Sudakov, B., Tomon, I., _The extremal number of tight cycles_. International Mathematics Research Notices (IMRN) (2022), 9663-9684.
-/

open SimpleGraph Finset

namespace Erdos576

/-- The $k$-dimensional hypercube graph $Q_k$: vertices are functions
$\operatorname{Fin} k \to \operatorname{Bool}$, and two vertices are adjacent iff they differ
in exactly one coordinate. -/
def hypercubeGraph (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := fun v ⟨hne, _⟩ => hne rfl

/-- The Turán number $\mathrm{ex}(n; H)$: the maximum number of edges in a simple graph
on $n$ vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬(H ⊑ F) ∧ F.edgeFinset.card = m}

/--
Erdős Conjecture (Problem 576) [Er64c], [ErSi70], [Er74c], [Er81], [Er93]:

Let $Q_3$ be the 3-dimensional hypercube graph. Erdős and Simonovits proved that
$$
  (1/2 + o(1)) \cdot n^{3/2} \leq \mathrm{ex}(n; Q_3) \ll n^{8/5}.
$$

Erdős conjectured that $\mathrm{ex}(n; Q_3) \asymp n^{8/5}$, i.e., there exist constants
$c, C > 0$ such that for all sufficiently large $n$,
$$
  c \cdot n^{8/5} \leq \mathrm{ex}(n; Q_3) \leq C \cdot n^{8/5}.
$$
-/
@[category research open, AMS 5]
theorem erdos_576 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ ((8 : ℝ) / 5) ≤ (turanNumber (hypercubeGraph 3) n : ℝ) ∧
      (turanNumber (hypercubeGraph 3) n : ℝ) ≤ C * (n : ℝ) ^ ((8 : ℝ) / 5) := by
  sorry

end Erdos576

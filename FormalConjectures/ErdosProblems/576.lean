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
# Erdős Problem 576

Erdős conjectured that the Turán number of the 3-dimensional hypercube graph $Q_3$
satisfies $\mathrm{ex}(n; Q_3) \asymp n^{8/5}$.

*Reference:* [erdosproblems.com/576](https://www.erdosproblems.com/576)

References: [Er64c], [ErSi70,p.378], [Er74c,p.78], [Er75], [Er81], [Er93,p.334]
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

/-- An injective graph homomorphism from $H$ to $G$: $G$ contains a copy of $H$
as a subgraph. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number $\mathrm{ex}(n; H)$: the maximum number of edges in a simple graph
on $n$ vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

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

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
# Erdős Problem 181

Burr and Erdős conjectured that the Ramsey number of the $n$-dimensional hypercube
graph $Q_n$ is at most linear in $2^n$, i.e., $R(Q_n) \ll 2^n$.

*Reference:* [erdosproblems.com/181](https://www.erdosproblems.com/181)

[BuEr75] Burr, S. A. and Erdős, P., *On the magnitude of generalized Ramsey numbers for graphs*.
Infinite and finite sets, Vol. 1 (1975), 214–240.

[Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
Quaestiones Mathematicae **16** (1993), 333–350.

[Ti22] Tikhomirov, K., *A remark on the Ramsey number of the hypercube*. arXiv:2208.14568 (2022).
-/

open SimpleGraph Finset

namespace Erdos181

/-- The $n$-dimensional hypercube graph $Q_n$: vertices are functions
$\operatorname{Fin} n \to \operatorname{Bool}$, and two vertices are adjacent iff they differ
in exactly one coordinate. -/
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
  loopless := fun v ⟨hne, _⟩ => hne rfl

/-- An injective graph homomorphism from $H$ to $G$: $G$ contains a (not necessarily
induced) copy of $H$ as a subgraph. -/
def ContainsCopy {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The diagonal Ramsey number $R(H)$: the minimum $N$ such that for every simple
graph $G$ on $\operatorname{Fin} N$, either $G$ or $G^c$ contains a copy of $H$. -/
noncomputable def ramseyDiag {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    ContainsCopy G H ∨ ContainsCopy Gᶜ H}

/--
Erdős Problem 181 [BuEr75]:

Let $Q_n$ be the $n$-dimensional hypercube graph. Prove that
$$R(Q_n) \ll 2^n,$$
i.e., there exists a constant $C > 0$ such that $R(Q_n) \leq C \cdot 2^n$ for all $n \geq 1$.
-/
@[category research open, AMS 5]
theorem erdos_181 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag (hypercubeGraph n) : ℝ) ≤ C * (2 ^ n : ℝ) := by
  sorry

/--
Tikhomirov (2022) [Ti22] proved that $R(Q_n) \ll 2^{(2-c)n}$ for some constant $c > 0$.
This is the best known upper bound toward Erdős Problem 181, improving over
the trivial $R(Q_n) \leq R(2^n) \leq 4^{2^n}$.
-/
@[category research solved, AMS 5]
theorem erdos_181_tikhomirov :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag (hypercubeGraph n) : ℝ) ≤ C * (2 : ℝ) ^ ((2 - c) * n) := by
  sorry

end Erdos181

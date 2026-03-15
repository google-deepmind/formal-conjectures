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
# Erdős Problem 578

*Reference:* [erdosproblems.com/578](https://www.erdosproblems.com/578)

A conjecture of Erdős and Bollobás [Er90c]. Solved by Riordan [Ri00], who in fact
proved this with any edge-probability $> 1/4$.

[Er90c] Erdős, P., *Problems and results in graph theory and combinatorics*. 1990.

[Ri00] Riordan, O., *Spanning subgraphs of random graphs*. Combinatorics, Probability
and Computing, 2000.
-/

open scoped Classical
open SimpleGraph

namespace Erdos578

/-- The $d$-dimensional hypercube graph $Q_d$. Vertices are functions `Fin d → Bool`
    (binary strings of length $d$). Two vertices are adjacent iff they differ in
    exactly one coordinate. -/
def hypercubeGraph (d : ℕ) : SimpleGraph (Fin d → Bool) where
  Adj u v := (Finset.univ.filter fun i => u i ≠ v i).card = 1
  symm := by
    intro u v h
    have heq : (Finset.univ.filter fun i : Fin d => v i ≠ u i) =
               (Finset.univ.filter fun i : Fin d => u i ≠ v i) := by
      ext i; simp [ne_comm]
    rw [heq]; exact h
  loopless := fun v h => by
    simp [Finset.filter_false_of_mem] at h

/-- The simple graph on `Fin n` determined by a Boolean matrix. Only values at
    `(min u v, max u v)` matter; this ensures symmetry. Under $G(n, 1/2)$, each
    Boolean matrix is equally likely, and the fraction of matrices whose graph
    has a property equals the probability that $G(n, 1/2)$ has that property. -/
def toGraph578 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := fun v ⟨h, _⟩ => h rfl

/--
Erdős Problem 578 [Er90c]:

In the Erdős–Rényi random graph $G(2^d, 1/2)$ — the uniform distribution over all
labelled simple graphs on $2^d$ vertices — the probability that $G$ contains a copy
of $Q_d$ (the $d$-dimensional hypercube) tends to $1$ as $d \to \infty$.

A copy of $Q_d$ in $G$ means an injective map $f$ from the vertices of $Q_d$ to the
vertices of $G$ such that adjacent vertices in $Q_d$ map to adjacent vertices in $G$.

Equivalently: for every $\varepsilon > 0$ there exists $d_0$ such that for all
$d \geq d_0$ the fraction of Boolean matrices on `Fin (2 ^ d)` whose graph contains
$Q_d$ is $\geq 1 - \varepsilon$.

Solved by Riordan [Ri00].
-/
@[category research solved, AMS 5 60]
theorem erdos_578 :
    ∀ ε : ℝ, ε > 0 →
    ∃ d₀ : ℕ, ∀ d : ℕ, d ≥ d₀ →
      ((Finset.univ.filter (fun ec : Fin (2 ^ d) → Fin (2 ^ d) → Bool =>
        (hypercubeGraph d).IsContained (toGraph578 ec))).card : ℝ) ≥
      (1 - ε) * (Fintype.card (Fin (2 ^ d) → Fin (2 ^ d) → Bool) : ℝ) := by
  sorry

end Erdos578

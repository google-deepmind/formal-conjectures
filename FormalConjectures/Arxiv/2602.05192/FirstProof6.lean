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
# Theorem 6

*Reference:* [arxiv/2602.05192](https://arxiv.org/abs/2602.05192)
**First Proof**
by *Mohammed Abouzaid, Andrew J. Blumberg, Martin Hairer, Joe Kileel, Tamara G. Kolda, Paul D. Nelson, Daniel Spielman, Nikhil Srivastava, Rachel Ward, Shmuel Weinberger, Lauren Williams*
-/

namespace Arxiv.«2602.05192»


open Matrix Polynomial SimpleGraph

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
For a graph $G = (V, E)$, let $G_S = (V, E(S,S))$ denote the graph with the same vertex set,
but only the edges between vertices in $S$.
Let $L$ be the Laplacian matrix of $G$ and let $L_S$ be the Laplacian of $G_S$.

I say that a set of vertices $S$ is $\epsilon$-light if the matrix $\epsilon L - L_S$ is
positive semidefinite.
-/
def IsEpsilonLight (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  letI G_S := G.induce S |>.spanningCoe
  letI L := lapMatrix ℝ G
  letI L_S := lapMatrix ℝ (G_S)
  PosSemidef (ε • L - L_S)

/--
Does there exist a constant $c > 0$ so that for every graph $G$ and every $\epsilon$ between
$0$ and $1$, $V$ contains an $\epsilon$-light subset $S$ of size at least $c \epsilon |V|$?

Note: While no proof of this is published yet, the authors of
[arxiv/2602.05192](https://arxiv.org/abs/2602.05192) announced that a proof will be released
on 2026-02-13.

TODO(firsching): update category and remove note when proof is published.
-/
@[category research open, AMS 5]
theorem epsilon_light_subset_exists : answer(sorry) ↔
    ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℝ),
    0 < ε → ε < 1 →
    ∃ (S : Finset (Fin n)), IsEpsilonLight G ε S ∧ (S.card : ℝ) ≥ c * ε * n := by
  sorry


end Arxiv.«2602.05192»

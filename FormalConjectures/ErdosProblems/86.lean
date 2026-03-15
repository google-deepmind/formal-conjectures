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
# Erdős Problem 86

*Reference:* [erdosproblems.com/86](https://www.erdosproblems.com/86)

This problem has a **$100** reward.

Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices
and $n \cdot 2^{n-1}$ edges). Is it true that every subgraph of $Q_n$ with
$\geq (\frac{1}{2} + o(1)) n \cdot 2^{n-1}$ many edges contains a $C_4$?

Equivalently, let $f(n)$ be the maximum number of edges in a subgraph of $Q_n$
without a $C_4$. The conjecture is that $f(n) \leq (\frac{1}{2} + o(1)) n \cdot 2^{n-1}$.

Erdős [Er91] showed that $f(n) \geq (\frac{1}{2} + c/n) n \cdot 2^{n-1}$ for some
constant $c > 0$. Brass, Harborth, and Nienborg [BHN95] improved the lower bound to
$f(n) \geq (\frac{1}{2} + c/\sqrt{n}) n \cdot 2^{n-1}$.

Balogh, Hu, Lidicky, and Liu [BHLL14] proved $f(n) \leq 0.6068 \cdot n \cdot 2^{n-1}$.
This was improved to $\leq 0.60318 \cdot n \cdot 2^{n-1}$ by Baber [Ba12b].

See also Problem 666 (the $C_6$ analogue) and OEIS A245762.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number
theory_. Graph Theory, Combinatorics, and Applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
397–406.

[Er92b] Erdős, P., _Some of my old and new problems in elementary number theory and
geometry_. Proceedings of the Fifth Canadian Number Theory Association Conference (1992).

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is
eighty, Vol. 2 (Keszthely, 1993), 97–132.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Discrete Math. 165/166 (1997), 227–231.

[Er95] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. 164 (1997), 81–85.

[Er97f] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
164 (1997), no. 1-3, 81–85.

[BHN95] Brass, P., Harborth, H., Nienborg, H., _On the maximum number of edges in a
C₄-free subgraph of Qₙ_. J. Graph Theory (1995), 17–23.

[BHLL14] Balogh, J., Hu, P., Lidický, B., Liu, H., _Upper bounds on the size of 4- and
6-cycle-free subgraphs of the hypercube_. European J. Combin. (2014), 75–85.

[Ba12b] Baber, R., _Turán densities of hypercubes_. arXiv:1201.3587 (2012).
-/

open SimpleGraph Finset

namespace Erdos86

/-- The $n$-dimensional hypercube graph $Q_n$. Vertices are functions
$\operatorname{Fin} n \to \operatorname{Bool}$, and two vertices are adjacent iff they differ
in exactly one coordinate. -/
noncomputable def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
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

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/--
Erdős Problem 86 [Er90][Er91][Er92b][Er93][Er94b][Er95][Er97f]:

Is it true that for every $\varepsilon > 0$, if $n$ is sufficiently large, every subgraph of
$Q_n$ with at least $(\frac{1}{2} + \varepsilon) \cdot n \cdot 2^{n-1}$ edges contains a $C_4$?
-/
@[category research open, AMS 5]
theorem erdos_86 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : SimpleGraph (Fin n → Bool),
      (∀ u v : Fin n → Bool, H.Adj u v → (hypercubeGraph n).Adj u v) →
      (↑(H.edgeFinset.card) : ℝ) ≥ (1 / 2 + ε) * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) →
      ∃ f : Fin 4 → (Fin n → Bool), Function.Injective f ∧
        ∀ i j, (cycleGraph 4 (by omega)).Adj i j → H.Adj (f i) (f j) := by
  sorry

end Erdos86

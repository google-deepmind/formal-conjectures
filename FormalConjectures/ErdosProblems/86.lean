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

[Er90][Er91][Er92b][Er93][Er94b][Er95][Er97f]
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

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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 720

*Reference:* [erdosproblems.com/720](https://www.erdosproblems.com/720)

Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such
that there is a graph $H$ with $m$ edges such that in any 2-colouring of the
edges of $H$ there is a monochromatic copy of $G$.

The original questions asked:
1. Is it true that $\hat{R}(P_n)/n \to \infty$?
2. Is it true that $\hat{R}(P_n)/n^2 \to 0$?
3. Is it true that $\hat{R}(C_n) = o(n^2)$?

Answered by Beck [Be83b], who proved the much stronger result that
$\hat{R}(P_n) \ll n$ and $\hat{R}(C_n) \ll n$ (i.e., the size Ramsey numbers are linear).

This resolves all three questions:
- Question 1 is answered in the negative ($\hat{R}(P_n)/n$ is bounded).
- Questions 2 and 3 are answered in the affirmative (in a much stronger form).

This problem carried a **$100 prize**. See also: Problem #559.

[Er76c] Erdős, P., _Problems in combinatorics and graph theory_ (1976), p. 5.

[EFRS78b] Erdős, P., Faudree, R.J., Rousseau, C.C., and Schelp, R.H., _The size Ramsey
number_, Periodica Mathematica Hungarica **9** (1978), 145–161.

[Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial
number theory_, Proceedings of the Ninth Southeastern Conference on Combinatorics,
Graph Theory, and Computing (1978), 29–40, p. 33.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica **1** (1981), 25–42.

[Er82e] Erdős, P., _Problems and results on finite and infinite combinatorial analysis II_,
1982.

[Be83b] Beck, J., _On size Ramsey number of paths, trees, and circuits I_,
J. Graph Theory **7** (1983), 115–129.
-/

open SimpleGraph

namespace Erdos720

/-- The path graph $P_n$ of length $n$: $n+1$ vertices $\{0, \ldots, n\}$ where vertex $i$
    is adjacent to vertex $i+1$. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := fun x h => by rcases h with h | h <;> omega

/-- The cycle graph $C_n$ on $n$ vertices ($n \geq 3$). Vertex $i$ is adjacent to
    vertex $(i+1) \bmod n$ and vertex $(i-1) \bmod n$. -/
def cycleGraph (n : ℕ) (_ : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % n ∨ i.val = (j.val + 1) % n)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/--
Erdős Problem 720, Part 1 (Beck's theorem for paths) [Be83b]:

The size Ramsey number of the path $P_n$ is at most linear in $n$.
That is, there exists a constant $C$ such that $\hat{R}(P_n) \leq C \cdot (n + 1)$ for all $n$.

This disproves the conjecture that $\hat{R}(P_n)/n \to \infty$ and proves
$\hat{R}(P_n)/n^2 \to 0$.
-/
@[category research solved, AMS 5]
theorem erdos_720 :
    ∃ C : ℕ, ∀ n : ℕ,
      sizeRamsey (pathGraph n) (pathGraph n) ≤ C * (n + 1) := by
  sorry

/--
Erdős Problem 720, Part 2 (Beck's theorem for cycles) [Be83b]:

The size Ramsey number of the cycle $C_n$ is at most linear in $n$.
That is, there exists a constant $C$ such that $\hat{R}(C_n) \leq C \cdot n$ for all $n \geq 3$.

This proves (in a much stronger form) the conjecture that $\hat{R}(C_n) = o(n^2)$.
-/
@[category research solved, AMS 5]
theorem erdos_720.variants.cycles :
    ∃ C : ℕ, ∀ n : ℕ, (hn : n ≥ 3) →
      sizeRamsey (cycleGraph n hn) (cycleGraph n hn) ≤ C * n := by
  sorry

end Erdos720

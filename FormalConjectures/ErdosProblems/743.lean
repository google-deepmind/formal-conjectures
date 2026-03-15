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
# Erdős Problem 743

*Reference:* [erdosproblems.com/743](https://www.erdosproblems.com/743)

Let $T_2, \ldots, T_n$ be a collection of trees such that $T_k$ has $k$ vertices.
Can we always write $K_n$ as the edge disjoint union of the $T_k$?

A conjecture of Gyárfás, known as the tree packing conjecture.

Gyárfás and Lehel proved that this holds if all but at most 2 of the trees are
stars, or if all the trees are stars or paths. Fishburn proved this for $n \leq 9$.
Bollobás proved that the smallest $\lfloor n/\sqrt{2} \rfloor$ many trees can always be packed
greedily into $K_n$.

Joos, Kim, Kühn, and Osthus proved this conjecture holds when the trees
have bounded maximum degree. Allen, Böttcher, Clemens, Hladký, Piguet, and Taraz
proved it holds when all trees have maximum degree at most $c \cdot n / \log n$ for
some constant $c > 0$. Janzer and Montgomery proved that there exists
some $c > 0$ such that the largest $cn$ trees can be packed into $K_n$.

[Er81] Erdős, P.
[ABCHPT21] Allen, P., Böttcher, J., Clemens, D., Hladký, J., Piguet, D., Taraz, A.,
  _The tree packing conjecture for trees of almost linear maximum degree_. arXiv:2106.11720 (2021).
-/

open SimpleGraph

namespace Erdos743

/--
**Erdős Problem 743** [Er81]:

Let $T_2, \ldots, T_n$ be any collection of trees such that $T_k$ has $k$ vertices.
Then the complete graph $K_n$ can be decomposed into edge-disjoint copies
of these trees. Also known as the tree packing conjecture (Gyárfás).
-/
@[category research open, AMS 5]
theorem erdos_743 : answer(sorry) ↔
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (T : (k : Fin (n - 1)) → SimpleGraph (Fin (k.val + 2))),
    (∀ k, (T k).IsTree) →
    ∃ (f : (k : Fin (n - 1)) → Fin (k.val + 2) → Fin n),
      -- Each embedding is injective
      (∀ k, Function.Injective (f k)) ∧
      -- The edge images are pairwise disjoint across different trees
      (∀ k₁ k₂, k₁ ≠ k₂ →
        ∀ a₁ b₁, (T k₁).Adj a₁ b₁ →
        ∀ a₂ b₂, (T k₂).Adj a₂ b₂ →
        Sym2.mk (f k₁ a₁, f k₁ b₁) ≠ Sym2.mk (f k₂ a₂, f k₂ b₂)) ∧
      -- Every edge of Kₙ is covered
      (∀ v w : Fin n, v ≠ w →
        ∃ k a b, (T k).Adj a b ∧
          Sym2.mk (v, w) = Sym2.mk (f k a, f k b)) := by
  sorry

end Erdos743

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 565

*References*:
- [erdosproblems.com/565](https://www.erdosproblems.com/565)
- [Ro73] V. Rödl, _The dimension of a graph and generalized Ramsey theorems_. thesis,
  Charles Univ. (1973).
- [KPR98] Y. Kohayakawa, H.-J. Prömel and V. Rödl, _Induced Ramsey numbers_. Combinatorica 18
  (1998), 373-404.
- [FoSu08] J. Fox and B. Sudakov, _Induced Ramsey-type theorems_. Adv. Math. 219 (2008),
  1771-1800.
- [CFS12] D. Conlon, J. Fox, and B. Sudakov, _On two problems in graph Ramsey theory_.
  Combinatorica 32 (2012), 513-535.
- [ACDFM25] L. Aragão, V. Campos, G. Dahia, J. Filipe, and J. P. Marciano,
  _An exponential upper bound for induced Ramsey numbers_ (2025).
-/

@[expose] public section

namespace Erdos565

open SimpleGraph

/-- The induced Ramsey number `R*(G)` -/
noncomputable def inducedRamseyNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ H : SimpleGraph (Fin m), ∀ c : H.edgeSet → Bool,
    ∃ (b : Bool) (S : Set (Fin m)),
      Nonempty (H.induce S ≃g G) ∧ ∀ e : H.edgeSet, (∀ x ∈ (e : Sym2 (Fin m)), x ∈ S) → c e = b}

/--
the minimal $m$ such that there is a graph $H$ on $m$ vertices such that any 2-colouring of
the edges of $H$ contains an induced monochromatic copy of $G$.

Is it true that $R*(G) <= 2^{O(n)}$ for any graph $G$ on $n$ vertices?
-/
@[category research open, question, AMS 5]
theorem erdos_565 :
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (inducedRamseyNumber G : ℝ) ≤ (2 : ℝ) ^ (C * (n : ℝ)) := by
  sorry

end Erdos565

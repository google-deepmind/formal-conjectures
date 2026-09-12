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

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Clique

/-!
# Shannon capacity of a graph

This file defines the tensor and strong products of simple graphs, the powers of a graph with
respect to the strong product, and the Shannon capacity
$$\Theta(G) = \sup_{n} \sqrt[n]{\alpha(G^{\boxtimes n})},$$
where $\alpha$ denotes the independence number. The Shannon capacity measures the effective
alphabet size of a noisy channel whose confusability graph is `G`.

## Main declarations

* `SimpleGraph.tensorProd`: the tensor product of two graphs.
* `SimpleGraph.strongProd`: the strong product of two graphs.
* `SimpleGraph.strongPow`: the powers of a graph with respect to the strong product.
* `SimpleGraph.shannonCapacity`: the Shannon capacity of a graph.

## Notation

* `G ⊠ H`: the strong product of `G` and `H`.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Shannon_capacity_of_a_graph)
-/

@[expose] public section

universe u

variable {α β : Type u}

namespace SimpleGraph

/-- Tensor product of simple graphs. `(a₁, b₁)` is adjacent to `(a₂, b₂)` if `a₁` is adjacent to
`a₂` and `b₁` is adjacent to `b₂`.

Replace once https://github.com/leanprover-community/mathlib4/pull/43170 lands.-/
def tensorProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm.symm x y h := by rwa [adj_comm G, adj_comm H]

/-- Strong product of simple graphs. It relates `(a₁, b₁)` and `(a₂, b₂)` if `a₁` and `a₂` are
equal or adjacent in `G`, and `b₁` and `b₂` are equal or adjacent in `H` (and `(a₁, b₁)` and
`(a₂, b₂)` are distinct).

Replace once https://github.com/leanprover-community/mathlib4/pull/43170 lands.-/
def strongProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) :=
  boxProd G H ⊔ tensorProd G H

@[inherit_doc] infixl:70 " ⊠ " => strongProd

/-- The power of a simple graph w. r. t. the strong product. -/
def strongPow (G : SimpleGraph α) : (n : ℕ) → SimpleGraph (Fin n → α)
  | 0 => completeGraph _
  | n + 1 => (Fin.succFunEquiv α n).symm.simpleGraph <| (strongPow G n) ⊠ G

/-- The Shannon capacity $\Theta(G) = \sup_n \sqrt[n]{\alpha(G^{\boxtimes n})}$ of a graph. -/
noncomputable def shannonCapacity (G : SimpleGraph α) : ℝ :=
  sSup {(↑α(G.strongPow n) : ℝ) ^ (↑n : ℝ)⁻¹ | n > 0}

end SimpleGraph

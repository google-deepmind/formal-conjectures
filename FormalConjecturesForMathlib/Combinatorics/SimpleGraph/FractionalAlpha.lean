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

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
Fractional alpha. This is defined as
$$
\max_x \sum_{v \in V} x_v
$$
subject to $0 \le x_v \le 1$ for all $v \in V$ and
$x_u + x_v \le 1$ whenever $(u, v)$ are connected by an edge.
-/
noncomputable def fractionalAlpha (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sSup {(∑ i, x i) | (x : α → ℝ) (_ : ∀ v, x v ∈ Set.Icc 0 1)
    (_ : ∀ u v, G.Adj u v → x u + x v ≤ 1)}


end SimpleGraph

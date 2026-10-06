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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The harmonic index of `G`, defined as `∑_{uv ∈ E(G)} 2 / (deg u + deg v)`,
where `deg` is the degree of a vertex. This is a standard topological index in
chemical graph theory, introduced by Fajtlowicz. -/
def harmonicIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (2 : ℚ) / ((G.degree u : ℚ) + (G.degree v : ℚ)),
      fun u v => by simp only [add_comm]⟩

end SimpleGraph

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

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace Digraph

variable {V W : Type*}

/--
A **tournament** is a directed graph in which every pair of distinct vertices is connected
by exactly one directed edge.
-/
def IsTournament (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

/--
An **orientation** of an undirected simple graph `H` is a digraph `D` whose edges
are obtained by directing each edge of `H` in exactly one direction.
-/
def IsOrientation (D : Digraph V) (H : SimpleGraph V) : Prop :=
  (∀ u v, D.Adj u v → H.Adj u v) ∧ (∀ u v, H.Adj u v → (D.Adj u v ↔ ¬ D.Adj v u))

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/--
The type of digraph homomorphisms `D →g D'`.
A function `f : V → W` is a digraph homomorphism if `D.Adj u v → D'.Adj (f u) (f v)`.
Note that `f` is a general mapping and is not required to be injective.
-/
structure Hom (D : Digraph V) (D' : Digraph W) where
  toFun : V → W
  map_adj' : ∀ {u v : V}, D.Adj u v → D'.Adj (toFun u) (toFun v)

infixl:50 " →g " => Digraph.Hom

instance (D : Digraph V) (D' : Digraph W) : CoeFun (D →g D') (fun _ => V → W) :=
  ⟨Digraph.Hom.toFun⟩

noncomputable instance (D : Digraph V) (D' : Digraph W) [DecidableRel D.Adj] [DecidableRel D'.Adj] :
    Fintype (D →g D') :=
  Fintype.ofInjective (fun f => f.toFun) (fun f g h => by cases f; cases g; congr)

/--
The number of homomorphisms from a digraph `D` to a digraph `D'`.
-/
noncomputable def homCount (D : Digraph V) (D' : Digraph W) [DecidableRel D.Adj] [DecidableRel D'.Adj] : ℕ :=
  Fintype.card (D →g D')

/--
The **homomorphism density** $t_D(D')$ of a digraph $D$ in a digraph $D'$.
It is defined as `#Hom(D, D') / |W|^{|V|}`.
-/
noncomputable def homDensity (D : Digraph V) (D' : Digraph W)
    [DecidableRel D.Adj] [DecidableRel D'.Adj] : ℝ :=
  (homCount D D' : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

end Digraph

/-
Copyright 2025 The Formal Conjectures Authors.

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
import Mathlib

universe u

variable {V : Type u} (G : SimpleGraph V)

namespace SimpleGraph

def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

variable {G}

def Subgraph.IsCritialVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

def Subgraph.IsCritialVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCritialVerts {v}

variable (G)

def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCritialVertex v

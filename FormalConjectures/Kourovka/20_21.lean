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
# Conjecture 20.21
by G. Verret and M. Conder
*Reference:* [The Kourovka Notebook](https://arxiv.org/pdf/1401.0300v50#page=160)
!-/

@[expose] public section
namespace Kourovka.«20.21»

/--
Does there exist a finite group $G$ with two normal subgroups $K$ and $L$, each with index $12$ in $G$, such that $K$ is isomorphic to $L$, but $G/K$ is isomorphic to $C_{12}$, while $G/L$ is isomorphic to $A_4$?
-/
@[category research open, question, AMS 20]
theorem kourovka_20_21 :
    ∃ (G : Type) (hG_Grp : Group G) (hG_fin : Finite G) (K L : Subgroup G) (hK : (K.index = 12) ∧ (K.Normal)) (hL : (L.index = 12) ∧ (L.Normal)),
    letI : K.Normal := hK.2
    letI : L.Normal := hL.2
    Nonempty (K ≃* L) ∧ IsCyclic (G⧸K) ∧ Nonempty (G⧸L ≃* alternatingGroup (Fin 4)) := by sorry

end Kourovka.«20.21»

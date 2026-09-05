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

import FormalConjecturesUtil

/-!
# TxGraffiti Conjecture 2: zero forcing versus independence (cubic graphs)

*Reference:* [arxiv/2507.17780](https://arxiv.org/abs/2507.17780)
**In Reverie Together: Ten Years of Mathematical Discovery with a Machine
Collaborator** by *Randy Davila, Boris Brimkov, Ryan Pepper*

Conjecture 2 (open since 2017) asserts that for every connected graph $G$ with
maximum degree at most $3$ and $G \ne K_4$,
$$Z(G) \le \alpha(G) + 1,$$
where $Z(G)$ is the zero forcing number and $\alpha(G)$ the independence number.
-/

open SimpleGraph

namespace Arxiv.«2507.17780»

/-- One step of the zero forcing colour-change rule: add to $S$ every vertex $w$
that is the unique neighbour of some $v \in S$ outside $S$. -/
noncomputable def zeroForcingStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun w =>
    w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ ∀ u, G.Adj v u → u ∉ S → u = w

/-- The zero forcing closure: iterate `zeroForcingStep` until it stabilises. -/
noncomputable def zeroForcingClosure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (zeroForcingStep G)^[Fintype.card V] S

/-- A set $S$ is a *zero forcing set* of $G$ if its zero forcing closure is all
of $V$. -/
def IsZeroForcingSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  zeroForcingClosure G S = Finset.univ

/-- The zero forcing number of a finite simple graph: the minimum cardinality of
a zero forcing set. -/
noncomputable def zeroForcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ IsZeroForcingSet G S}

/--
TxGraffiti [Conjecture 2](https://arxiv.org/abs/2507.17780):
for every connected graph $G$ with $\Delta(G) \le 3$ and $G \ne K_4$,
$$Z(G) \le \alpha(G) + 1.$$

This conjecture is **open**.
-/
@[category research open, AMS 5]
theorem tx_graffiti_conjecture_2 (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected)
    (_hDeg : G.maxDegree ≤ 3) (_hNotK4 : G ≠ ⊤) :
    zeroForcingNumber G ≤ G.indepNum + 1 := by
  sorry

end Arxiv.«2507.17780»

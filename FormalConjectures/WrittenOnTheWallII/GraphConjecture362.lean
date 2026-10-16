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
# Written on the Wall II — Conjecture 362

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 362, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A sharp support-component diameter bound proving Graffiti.pc Conjecture 362](https://github.com/user-attachments/files/33357078/Gebendorfer_362_Intake_2026-10-12.zip)

The manuscript proves the original tree claim through a stronger diameter bound
for connected graphs. Its current copy is undated. Components include isolated
vertices, with zero components on the empty induced graph.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture362
open SimpleGraph Finset

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1

noncomputable def componentsOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

/-- Every finite simple tree of order greater than two satisfies
$\gamma_t(T)\ge c(T[S(T)\cup L(T)])+(1+rad(T))/3$.
The fraction is rational and is not rounded down. The radius is finite on this
domain, so its natural value is obtained from Mathlib's extended radius.
-/
@[category research solved, AMS 5]
theorem conjecture362 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 2 < Fintype.card V) :
    (componentsOn T (supports T ∪ leaves T) : ℚ) +
      (1 + (T.radius.toNat : ℚ)) / 3 ≤ T.totalDominationNumber := by
  sorry

/-- Gebendorfer's stronger bound holds for every connected finite simple graph
of order at least three:
$diam(G)+1\le5(\gamma_t(G)-c(G[S(G)]))$.
The subtraction is expressed in the integers, preserving its meaning even
before deriving that the domination number exceeds the component count.
-/
@[category research solved, AMS 5]
theorem conjecture362_diameter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    (G.diam : ℤ) + 1 ≤ 5 * ((G.totalDominationNumber : ℤ) -
      (componentsOn G (supports G) : ℤ)) := by
  sorry

/-- Adjoining each leaf to its unique support changes no component count in a
connected finite simple graph of order at least three.
-/
@[category research solved, AMS 5]
theorem support_components_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    componentsOn G (supports G ∪ leaves G) = componentsOn G (supports G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture362

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
# Written on the Wall II — Conjecture 379

*References:*
- [E. DeLaVina, C. E. Larson, R. Pepper and B. Waller, Graffiti.pc on the total domination number of a tree, Section 3, Conjecture 1](https://math1um.github.io/Research/r05.pdf)
- [J. J. Gebendorfer, Maximum-degree components and degree diversity in totally dominated trees, 14 October 2026](https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip)

The primary paper states the conjecture for nontrivial trees. The written proof
covers that domain, including $K_2$, and gives a stronger bound for every total
dominating set when the order is at least three. Maximum degrees are ambient
degrees in the original tree.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture379
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def componentsOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

def degreeDiversity (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.image fun v => G.degree v).card

/-- Every nontrivial finite simple tree satisfies
$\gamma_t(T)\ge c(T[M])+dd(T)/3$, where $M$ is the full ambient
maximum-degree set and $dd(T)$ counts distinct degree values. The fraction is
rational and the component count includes isolates.
-/
@[category research solved, AMS 5]
theorem conjecture379 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V) :
    (componentsOn T (maximumVertices T) : ℚ) + (degreeDiversity T : ℚ) / 3 ≤
      T.totalDominationNumber := by
  sorry

/-- For every total dominating set $D$ in a finite simple tree of order at
least three, $|D|\ge c(T[M])+\max\{1,(dd(T)-1)/2\}$.
The rational difference and half are retained, without natural subtraction
or downward rounding.
-/
@[category research solved, AMS 5]
theorem conjecture379_strengthened (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    (componentsOn T (maximumVertices T) : ℚ) + max 1 (((degreeDiversity T : ℚ)-1)/2) ≤
      (D.card : ℚ) := by
  sorry

end WrittenOnTheWallII.GraphConjecture379

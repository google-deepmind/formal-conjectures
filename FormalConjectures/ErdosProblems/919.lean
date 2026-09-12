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
# Erdős Problem 919

*References:*
- [erdosproblems.com/919](https://www.erdosproblems.com/919)
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
-/

universe u

open Cardinal Ordinal
open scoped Cardinal Ordinal

namespace Erdos919

/-- The ordinal $\omega_2^2$ realised as a type of vertices. -/
abbrev Omega2Sq : Type u := ((ω_ 2 : Ordinal.{u}) ^ 2).ToType

/--
Is there a graph $G$ with vertex set $\omega_2^2$ and chromatic number $\aleph_2$ such that every
subgraph whose vertices have a lesser type has chromatic number $\leq \aleph_0$?

Here $\omega_2^2$ is the ordinal square $\omega_2\cdot\omega_2$, and a set of vertices has lesser
type when its order type (as a subset of $\omega_2^2$) is strictly smaller than $\omega_2^2$.
-/
@[category research open, AMS 3 5]
theorem erdos_919 :
    answer(sorry) ↔
      ∃ (G : SimpleGraph Omega2Sq), G.chromaticCardinal = ℵ_ 2 ∧
        ∀ (W : Set Omega2Sq), typeLT W < ω_ 2 ^ 2 →
          (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
What if instead we ask for $G$ to have chromatic number $\aleph_1$?
-/
@[category research open, AMS 3 5]
theorem erdos_919.variants.chromaticCardinal_aleph_1 :
    answer(sorry) ↔
      ∃ (G : SimpleGraph Omega2Sq), G.chromaticCardinal = ℵ₁ ∧
        ∀ (W : Set Omega2Sq), typeLT W < ω_ 2 ^ 2 →
          (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
Erdős and Hajnal constructed a graph on $\omega_1^2$ with chromatic number $\aleph_1$ such that
every strictly smaller subgraph has chromatic number $\leq \aleph_0$. The vertices are the pairs
$(x_\alpha, y_\beta)$ for $1\leq \alpha,\beta < \omega_1$, ordered lexicographically, with an edge
between $(x_{\alpha_1}, y_{\beta_1})$ and $(x_{\alpha_2}, y_{\beta_2})$ if and only if
$\alpha_1 < \alpha_2$ and $\beta_1 < \beta_2$.
-/
@[category research solved, AMS 3 5]
theorem erdos_919.variants.erdos_hajnal_omega1_sq :
    ∃ (G : SimpleGraph ((ω_ 1 : Ordinal.{u}) ^ 2).ToType),
      G.chromaticCardinal = ℵ₁ ∧
        ∀ (W : Set ((ω_ 1 : Ordinal.{u}) ^ 2).ToType), typeLT W < ω_ 1 ^ 2 →
          (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/--
A similar construction produces a graph on $\omega_2^2$ with chromatic number $\aleph_2$ such that
every smaller subgraph has chromatic number $\leq \aleph_1$.
-/
@[category research solved, AMS 3 5]
theorem erdos_919.variants.omega2_sq_aleph_1_bound :
    ∃ (G : SimpleGraph Omega2Sq), G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set Omega2Sq), typeLT W < ω_ 2 ^ 2 →
        (G.induce W).chromaticCardinal ≤ ℵ₁ := by
  sorry

/--
A theorem of Babai: if $G$ is a graph on a well-ordered set with chromatic number
$\geq \aleph_0$, there is a subgraph on vertices with order-type $\omega$ with chromatic number
$\aleph_0$.
-/
@[category research solved, AMS 3 5]
theorem erdos_919.variants.babai {V : Type u} [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (hχ : ℵ₀ ≤ G.chromaticCardinal) :
    ∃ (H : G.Subgraph), typeLT H.verts = ω ∧ H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- The vertex type of the main problem has order type $\omega_2^2$. -/
@[category test, AMS 3 5]
theorem typeLT_omega2Sq : typeLT Omega2Sq = (ω_ 2 : Ordinal.{u}) ^ 2 :=
  type_toType _

end Erdos919

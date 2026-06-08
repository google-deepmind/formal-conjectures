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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 601

*Reference:* [erdosproblems.com/601](https://www.erdosproblems.com/601)

*References:*
- [EHM70] Erdős, P.; Hajnal, A.; Milner, E.C. *On sets of almost disjoint subsets of a set.*
  Acta Math. Acad. Sci. Hungar. (1968), 209–218.
- [La90] Larson, J.A. *Martin's Axiom and ordinal graphs: large independent sets or infinite
  paths.* European J. Combin. (1990), 117–124.
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos601

universe u

/--
`HasPathOrIndepSetOfType α` holds for an ordinal $\alpha$ if every simple graph on
$\alpha.\mathrm{ToType}$ contains either:

1. an **infinite path** — an injective function $f : \mathbb{N} \to \alpha.\mathrm{ToType}$
   with $G.\mathrm{Adj}\, (f n)\, (f(n+1))$ for all $n$, or
2. an **independent set of order type $\alpha$** — a set $s \subseteq \alpha.\mathrm{ToType}$
   that is pairwise non-adjacent in $G$ and whose order type (under the well-order inherited
   from $\alpha$) equals $\alpha$.
-/
def HasPathOrIndepSetOfType (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    (∃ f : ℕ → α.ToType, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
    (∃ s : Set α.ToType, G.IsIndepSet s ∧ typeLT s = α)

/--
**Erdős Problem 601** ($500 prize).

For which limit ordinals $\alpha$ does `HasPathOrIndepSetOfType α` hold?
-/
@[category research open, AMS 5]
theorem erdos_601 :
    ∀ α : Ordinal.{0}, Order.IsSuccLimit α →
      (HasPathOrIndepSetOfType α ↔
        (answer(sorry) : Ordinal.{0} → Prop) α) := by
  sorry

/--
**Universal variant**: the strong statement that `HasPathOrIndepSetOfType α` holds for
*every* limit ordinal $\alpha$. -/
@[category research open, AMS 5]
theorem erdos_601.variants.universal :
    answer(sorry) ↔
    ∀ α : Ordinal.{0}, Order.IsSuccLimit α → HasPathOrIndepSetOfType α := by
  sorry

namespace erdos_601.variants

/--
**Erdős–Hajnal–Milner (1970)** [EHM70]: For all limit ordinals $\alpha < \omega_1^{\omega+2}$,
every graph on $\alpha.\mathrm{ToType}$ has either an infinite path or an independent set of
order type $\alpha$.
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_milner_1970 :
    ∀ α : Ordinal.{0},
      Order.IsSuccLimit α →
      α < ω_ 1 ^ (ω + 2) →
      HasPathOrIndepSetOfType α := by
  sorry

/--
**$250 sub-question at $\omega_1^{\omega+2}$**: Does `HasPathOrIndepSetOfType (ω₁^{ω+2})` hold?

Erdős offered $250 specifically for this case, the first ordinal not covered by the
Erdős–Hajnal–Milner theorem.
-/
@[category research open, AMS 5]
theorem omega_1_omega_plus_2 :
    HasPathOrIndepSetOfType (ω_ 1 ^ (ω + 2)) := by
  sorry

/-
**Larson (1990)** [La90] showed that under Martin's Axiom (MA), the property
`HasPathOrIndepSetOfType α` holds for all limit ordinals $\alpha < 2^{\aleph_0}$. We do
not state this here as a Lean theorem because Martin's Axiom is not yet formalised in
Mathlib (and a bare `MA : Prop` placeholder would not faithfully encode the axiom).
-/

/--
**Base case $\alpha = \omega$**: `HasPathOrIndepSetOfType ω` holds.

Every countably infinite graph on vertex set $\omega$ either contains an infinite path or
has an infinite independent set (and an infinite set has order type $\omega$). Follows from
Ramsey-theoretic arguments (or directly from the Erdős–Hajnal–Milner result since
$\omega < \omega_1^{\omega+2}$).
-/
@[category research solved, AMS 5]
theorem at_omega : HasPathOrIndepSetOfType ω := by
  sorry

end erdos_601.variants

end Erdos601

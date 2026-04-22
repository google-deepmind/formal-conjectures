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
import FormalConjectures.Util.ProblemImports

open Cardinal Ordinal

open scoped Cardinal Ordinal

/-!
# Erdős Problem 1173

**Verbatim statement (Erdős #1173, status O):**
> Assume the generalised continuum hypothesis. Let\[f: \omega_{\omega+1}\to [\omega_{\omega+1}]^{\leq \aleph_\omega}\]be a set mapping such that\[\lvert f(\alpha)\cap f(\beta)\rvert <\aleph_\omega\]for all $\alpha\neq \beta$. Does there exist a free set of cardinality $\aleph_{\omega+1}$?

**Source:** https://www.erdosproblems.com/1173

**Notes:** OPEN


*Reference:* [erdosproblems.com/1173](https://www.erdosproblems.com/1173)

*References:*
- [EH74] Erdős, Paul and Hajnal, András, Unsolved and solved problems in set theory.
  Proceedings of the Tarski symposium (1974), 269–287.

## Problem Statement

Assume GCH. Let $f : \omega_{\omega+1} \to [\omega_{\omega+1}]^{\leq \aleph_\omega}$ be a
**set mapping** — a function assigning to each element $\alpha \in \omega_{\omega+1}$ a subset
$f(\alpha) \subseteq \omega_{\omega+1}$ of cardinality at most $\aleph_\omega$ — such that
for all $\alpha \neq \beta$ in $\omega_{\omega+1}$, the intersection $f(\alpha) \cap f(\beta)$
has cardinality strictly less than $\aleph_\omega$.

Does there exist a **free set** of cardinality $\aleph_{\omega+1}$? That is, a set
$Y \subseteq \omega_{\omega+1}$ with $|Y| = \aleph_{\omega+1}$ such that for all
$\alpha \neq \beta$ in $Y$, $\beta \notin f(\alpha)$.

A problem of Erdős and Hajnal [EH74].

## Overview

The key definitions are:
- `IsSetMapping f`: the set mapping condition — each image has cardinality $\leq \aleph_\omega$
  and the images are pairwise almost disjoint (intersections have cardinality $< \aleph_\omega$).
- `IsFreeSet f Y`: the free set condition — $Y$ is free for $f$ if for all distinct
  $\alpha, \beta \in Y$, $\beta \notin f(\alpha)$.
- `GCH`: the Generalized Continuum Hypothesis, taken as an abstract hypothesis `Prop`.

The domain is the initial ordinal $\omega_{\omega+1}$ (the $(\omega+1)$-th uncountable
initial ordinal), realized as a type via `Ordinal.ToType`.
The target cardinal $\aleph_\omega = $ `ℵ_ ω` and $\aleph_{\omega+1} = $ `ℵ_ (ω + 1)`.
-/

namespace Erdos1173

/-- The **Generalized Continuum Hypothesis**: for every ordinal `o`, $2^{\aleph_o} = \aleph_{o+1}$.

This is an axiom independent of ZFC; it is taken here as an abstract hypothesis `Prop` to be
passed explicitly where needed. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)

/-- The **set mapping condition** for a function
$f : \omega_{\omega+1} \to \mathcal{P}(\omega_{\omega+1})$.

We require:
1. Each image $f(\alpha)$ has cardinality at most $\aleph_\omega$.
2. For any two distinct elements $\alpha \neq \beta$, the intersection
   $f(\alpha) \cap f(\beta)$ has cardinality strictly less than $\aleph_\omega$.

Here the domain is the type `(ω_ (ω + 1)).ToType` corresponding to the initial ordinal
$\omega_{\omega+1}$, and `Set (ω_ (ω + 1)).ToType` is the powerset. -/
def IsSetMapping (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) : Prop :=
  (∀ α : (ω_ (ω + 1)).ToType, #(f α) ≤ ℵ_ ω) ∧
  (∀ α β : (ω_ (ω + 1)).ToType, α ≠ β → #(f α ∩ f β : Set (ω_ (ω + 1)).ToType) < ℵ_ ω)

/-- A set $Y \subseteq \omega_{\omega+1}$ is **free** for the set mapping $f$ if for all
distinct $\alpha, \beta \in Y$, we have $\beta \notin f(\alpha)$.

Equivalently: no element of $Y$ is "captured" by the image of any other element of $Y$ under $f$. -/
def IsFreeSet (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (Y : Set (ω_ (ω + 1)).ToType) : Prop :=
  ∀ α ∈ Y, ∀ β ∈ Y, α ≠ β → β ∉ f α

/--
**Erdős–Hajnal Problem 1173**: Assume GCH. Let $f : \omega_{\omega+1} \to [\omega_{\omega+1}]^{\leq
\aleph_\omega}$ be a set mapping such that $|f(\alpha) \cap f(\beta)| < \aleph_\omega$ for all
$\alpha \neq \beta$. Does there exist a free set of cardinality $\aleph_{\omega+1}$?

More precisely: under GCH, for every function $f$ satisfying the set mapping condition
`IsSetMapping f`, must there exist a free set $Y$ with $|Y| = \aleph_{\omega+1}$?

*A problem of Erdős and Hajnal [EH74].*

**Status:** OPEN.

**Formalization notes:**
- GCH is passed as an explicit hypothesis `hGCH : GCH`, following the convention for
  set-theoretic problems whose status may depend on additional axioms.
- The domain $\omega_{\omega+1}$ is encoded via `Ordinal.ToType`, so that `f` has type
  `(ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType`.
- `ω` in `ω_ (ω + 1)` is `Ordinal.omega0` (the first infinite ordinal), available via
  `open scoped Ordinal`. Similarly `ℵ_ ω` and `ℵ_ (ω + 1)` use `open scoped Cardinal`.
-/
@[category research open, AMS 3]
theorem erdos_1173 : answer(sorry) ↔
    GCH →
    ∀ f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType,
      IsSetMapping f →
      ∃ Y : Set (ω_ (ω + 1)).ToType, IsFreeSet f Y ∧ #Y = ℵ_ (ω + 1) := by
  sorry

/- ## Sanity checks and auxiliary lemmas -/

/--
**Cardinality check**: The initial ordinal $\omega_{\omega+1}$ has cardinality $\aleph_{\omega+1}$.

This confirms that the domain type `(ω_ (ω + 1)).ToType` has the right cardinality. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.card_domain :
    #(ω_ (ω + 1)).ToType = ℵ_ (ω + 1) := by
  rw [mk_toType, Ordinal.card_omega]

/--
**Cardinality ordering**: $\aleph_\omega < \aleph_{\omega+1}$.

This ensures the free set size $\aleph_{\omega+1}$ is strictly larger than the bound
$\aleph_\omega$ on image sizes, making the problem non-trivial. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.aleph_omega_lt_succ : ℵ_ ω < ℵ_ (ω + 1) := by
  exact Cardinal.aleph_lt_aleph.mpr (Order.lt_succ ω)

/--
**Well-definedness of `IsFreeSet`**: The empty set is always a free set for any mapping `f`.

This is a trivial sanity check showing `IsFreeSet` is non-vacuously definable. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.empty_is_free
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) :
    IsFreeSet f ∅ := by
  intro _ hα
  simp at hα

/--
**Well-definedness of `IsFreeSet`**: A singleton $\{\alpha\}$ is always a free set for any `f`.

For a singleton, the condition `α ≠ β` with `α, β ∈ {α}` is never satisfied, so the predicate
holds vacuously. -/
@[category test, AMS 3]
theorem erdos_1173.sanity.singleton_is_free
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (α : (ω_ (ω + 1)).ToType) :
    IsFreeSet f {α} := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  exact absurd (ha ▸ hb ▸ rfl) hab

/--
**Monotonicity of `IsFreeSet`**: If $Y$ is a free set and $Z \subseteq Y$, then $Z$ is also free.

Free sets are downward-closed under inclusion. -/
@[category undergraduate, AMS 3]
theorem erdos_1173.variants.free_set_mono
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    {Y Z : Set (ω_ (ω + 1)).ToType}
    (hYZ : Z ⊆ Y) (hY : IsFreeSet f Y) : IsFreeSet f Z := by
  intro α hα β hβ hne
  exact hY α (hYZ hα) β (hYZ hβ) hne

/--
**Relation to the set mapping bound**: Under `IsSetMapping f`, the image of each element
has cardinality strictly less than $\aleph_{\omega+1}$.

Since $|f(\alpha)| \leq \aleph_\omega < \aleph_{\omega+1}$, each image is strictly smaller
than the full domain. -/
@[category undergraduate, AMS 3]
theorem erdos_1173.variants.image_lt_aleph_succ
    (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (hf : IsSetMapping f)
    (α : (ω_ (ω + 1)).ToType) :
    #(f α) < ℵ_ (ω + 1) := by
  exact (hf.1 α).trans_lt (Cardinal.aleph_lt_aleph.mpr (Order.lt_succ ω))

end Erdos1173

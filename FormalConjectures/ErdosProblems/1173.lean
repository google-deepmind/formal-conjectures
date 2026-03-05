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
# Erdős Problem 1173

*Reference:* [erdosproblems.com/1173](https://www.erdosproblems.com/1173)

[Ko25b] Koepke, P., Problem 35.

[Va99] Vaughan, J.E., 7.88.

A problem of Erdős and Hajnal.
-/

open Ordinal Cardinal

namespace Erdos1173

/-- The Generalized Continuum Hypothesis: $2^{\aleph_\alpha} = \aleph_{\alpha+1}$ for all
ordinals $\alpha$. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- $\omega_{\omega+1}$, the initial ordinal of $\aleph_{\omega+1}$. -/
noncomputable def omegaOmega1 : Ordinal := (aleph (ω + 1)).ord

/-- A set $H \subseteq \omega_{\omega+1}$ is free for $f$ if for all $\alpha \in H$,
$f(\alpha) \cap H \subseteq \{\alpha\}$,
i.e., $\alpha \notin f(\beta)$ for all distinct $\alpha, \beta \in H$. -/
def IsFreeSet (f : {α : Ordinal // α < omegaOmega1} → Set {α : Ordinal // α < omegaOmega1})
    (H : Set {α : Ordinal // α < omegaOmega1}) : Prop :=
  ∀ α ∈ H, f α ∩ H ⊆ {α}

/--
Erdős Problem 1173 [Ko25b, Problem 35] [Va99, 7.88]:

Assuming the Generalised Continuum Hypothesis, let
$f : \omega_{\omega+1} \to [\omega_{\omega+1}]^{\leq \aleph_\omega}$
be a set mapping such that $|f(\alpha) \cap f(\beta)| < \aleph_\omega$ for all
$\alpha \neq \beta$.
Does there exist a free set of cardinality $\aleph_{\omega+1}$?

Here $\omega_{\omega+1} = (\aleph_{\omega+1}).\mathrm{ord}$ is the initial ordinal of
$\aleph_{\omega+1}$, elements are ordinals $\alpha < \omega_{\omega+1}$, and a free set $H$
satisfies $f(\alpha) \cap H \subseteq \{\alpha\}$ for all $\alpha \in H$.
The cardinality comparison uses `Cardinal.lift` to reconcile universe levels:
subsets of $\{\alpha : \mathrm{Ordinal} \mid \alpha < \omega_{\omega+1}\}$ live in `Type 1`,
while `aleph` lives in `Cardinal.{0}`; `Cardinal.lift.{1,0}` embeds `Cardinal.{0}` into
`Cardinal.{1}`.

A problem of Erdős and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1173 : answer(sorry) ↔
    ∀ (h : GCH)
      (f : {α : Ordinal // α < omegaOmega1} → Set {α : Ordinal // α < omegaOmega1})
      (hf : ∀ α : {x : Ordinal // x < omegaOmega1},
        Cardinal.mk ↥(f α) ≤ Cardinal.lift.{1, 0} (aleph ω))
      (hfI : ∀ α β : {x : Ordinal // x < omegaOmega1}, α ≠ β →
        Cardinal.mk ↥(f α ∩ f β) < Cardinal.lift.{1, 0} (aleph ω)),
    ∃ H : Set {α : Ordinal // α < omegaOmega1},
      IsFreeSet f H ∧ Cardinal.lift.{1, 0} (aleph (ω + 1)) ≤ Cardinal.mk ↥H := by
  sorry

end Erdos1173

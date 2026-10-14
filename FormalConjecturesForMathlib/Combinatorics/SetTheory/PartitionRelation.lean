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

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

/-!
# Cardinal partition relation

This file defines `Combinatorics.cardinalPartitionRel`, the multicolor
$r$-uniform partition arrow

  $$\mu \to (\nu_\alpha)_{\alpha < \gamma}^r$$

between an infinite "source" cardinal $\mu$, a uniformity $r$, an ordinal-indexed
family of "target" cardinals $\nu_\alpha$, and a coloring of $r$-element subsets.
This is the standard notation in infinitary combinatorics and is reused by
several Erdős–Rado-style problems.
-/

namespace Combinatorics

open Cardinal

universe u

/--
`cardinalPartitionRel μ r γ ν` asserts the multicolor $r$-uniform partition relation
$$\mu \to (\nu_\alpha)_{\alpha < \gamma}^r.$$

It states: for every type `A` with `#A = μ` and every coloring `col` of the
$r$-element finite subsets of `A` by `γ.ToType` (the colors indexed by
ordinals less than `γ`), there exists a color `i : γ.ToType` and a
homogeneous subset `H : Set A` with `#H = ν i` such that every $r$-element
subset of `H` receives color `i`.

When `γ = 2` and `r = 2` this reduces to the classical binary partition
relation $\mu \to (\nu_0, \nu_1)^2$.
-/
def cardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A),
        #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

end Combinatorics

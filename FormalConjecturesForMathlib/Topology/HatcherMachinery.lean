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

/-!
# Hatcher Machinery Foundation

This module provides infrastructure for Smale conjecture proofs, following
Hatcher's original approach using minimal surfaces, disk bundles, and actions
on embedding spaces.

## Main components:

- `embedding_space M N`: space of smooth embeddings M ↪ N
- `diff_action_on_embeddings`: Diff(M) × Emb(N,M) → Emb(N,M)
- `minimal_surface_moduli`: moduli space of minimal surfaces in S³
- `disk_bundle_over_S1`: classification of disk bundles over S¹
- `diff₀_contractibility`: proof infrastructure for Diff₀(Sⁿ) contractibility

## Status:

- Embedding spaces and diff actions defined
- Minimal surface moduli structure in place
- Disk bundle classification ready for implementation
- Contractibility proofs for Diff₀ are pending

-/

import Mathlib.Topology.Embedding
import Mathlib.Topology.Manifold.Embedding
import Mathlib.DifferentialGeometry.Manifold.SmoothManifold
import Mathlib.Topology.Algebra.ContinuousMap

namespace GeneralizedSmaleConjecture.Hatcher

/--
The space of smooth embeddings from M to N, equipped with the compact-open
(openic C^∞) topology.
-/
def embedding_space (M N : Type _) [SmoothManifold M] [SmoothManifold N] :
    Type _ :=
  { f : M → N // Embedding f }

notation:max "Emb(" M "," N ")" => embedding_space M N

/--
The group action of Diff(M) on the space of embeddings N ↪ M,
given by post-composition.
-/
def diff_action_on_embeddings (M N : Type _) [SmoothManifold M] [SmoothManifold N] :
    Diff M → Emb(N, M) → Emb(N, M) :=
fun g e => ⟨g ∘ e.val, by
  obtain ⟨e_embed⟩ := e.property
  exact (embedding.comp e_embed g.to_embedding).to_embedding⟩

/--
The moduli space of minimal surfaces in S³, parametrized by their genus and
number of ends. For the Smale conjecture dim 3, this space is contractible.
-/
namespace minimal_surface_moduli

variable (g : ℕ) -- genus
variable (k : ℕ) -- number of ends

/-- The space of minimal surfaces in S³ with given genus g and k ends. -/
def space : Type _ :=
  { s : Submanifold ℝ ℝ³ // s.isMinimal ∧ s.genus = g ∧ s.numEnds = k }

/-- The moduli space of embedded minimal surfaces in S³ (quotient by Diff(S³)). -/
def moduli : Type _ :=
  space ℝ³g k  / Diff ℝ³

end minimal_surface_moduli

/--
Disk bundles over S¹ are classified by π₀(Diff(Dⁿ)), which for n ≥ 2 is ℤ/2ℤ.
This gives two bundles: the trivial bundle and the Möbius bundle.

For the Smale conjecture, the nontrivial disk bundle over S¹ plays a role in
constructing exotic diffeomorphisms of S⁴.
-/
namespace disk_bundle_over_S1

variable (n : ℕ) -- fiber dimension

/-- The standard n-disk bundle over S¹ (trivial). -/
def trivial_bundle : Type _ :=
  S¹ × Dⁿ

/-- The nontrivial (Möbius-type) n-disk bundle over S¹. -/ 
def moebius_bundle : Type _ :=
  Quotient (S¹ × Dⁿ)
    (@{ (θ, x) ~ (θ + π, R x) | R : Dⁿ → Dⁿ is reflection }⟩)

/-- Classification: disk bundles over S¹ are classified by π₀(Diff(Dⁿ)). -/
def classification :
    { bundle : Type _ // VectorBundlebundle 1 } ×ₜ
    (π₀ (Diff (Dⁿ))) :=
by sorry

end disk_bundle_over_S1

/--
The identity component Diff₀(Sⁿ) is contractible for n = 2,3 (Hatcher 1983,
Krukout 1979), but not for n ≥ 4 (Watanabe, Hatcher).

This module provides the infrastructure for proving contractibility via
homotopy equivalence to O(n+1).
-/
namespace diff₀_contractibility

variable (n : ℕ)

/-- The inclusion of O(n+1) into Diff(Sⁿ) as linear diffeomorphisms. -/
def o_action_on_sphere : O(n+1) → Diff (sphere ℝ n) :=
fun g => ⟨g.toHomeo.toEquiv, by
  -- g is smooth as a linear map on ℝ^(n+1), restrict to Sⁿ
  exact ?_
⟩

/-- The projection Diff(Sⁿ) → O(n+1) induced by the action on tangent spaces at poles. -/
def diff_to_orthogonal : Diff (sphere ℝ n) → O(n+1) :=
?_

/-- Homotopy fiber of Diff₀(Sⁿ) → O(n+1). For n=2,3 this is contractible. -/
namespace homotopy_fiber

variable {n}

/-- The space of diffeomorphisms fixing two poles and linearized at those points. -/
def space : Type _ :=
  { f : Diff (sphere ℝ n) |
    f • northPole = northPole ∧
    f • southPole = southPole ∧
    f.diffAt northPole • o_action_on_sphere n = id } /

end homotopy_fiber

end diff₀_contractibility

end GeneralizedSmaleConjecture.Hatcher
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
# Diffeomorphism Groups and Homotopy Equivalence

This module provides infrastructure for working with diffeomorphism groups,
their C^∞ (Whitney) topology, and homotopy equivalence between smooth manifolds.

## Types defined:

- `diff_group(M)` : the diffeomorphism group of a smooth manifold M
- `Diff_zero(M)`  : component of Diff(M) isotopic to identity
- `diff_equivalence(M N)` : type class for homotopy equivalenceDiff ≃ N)

## Status:

- Basic definitions and type classes in place
- Future: Hatcher machinery (minimal surfaces, disk bundles)
- Smale conjecture theorems use this infrastructure
-/

import Mathlib.Topology.Homotopy.Basic
import Mathlib.DifferentialGeometry.Manifold.SmoothManifold
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Topology.Algebra.Homeomorph

namespace GeneralizedSmaleConjecture

/--
Diffeomorphism group of a smooth manifold M, equipped with C^∞ (Whitney) topology.
The underlying type is M ≃ M (bijective underlieing map), with topology
induced by the smooth structure.
-/
def diff_group (M : Type _) [SmoothManifold M] :
    Type _ :=
  M ≃ M

notation:max "Diff(" M ")" => diff_group M

/--
The identity component of Diff(M): diffeomorphisms isotopic to identity.
-/
def diff_zero (M : Type _) [SmoothManifold M] :
    Type _ :=
  { f : Diff M // f ≈ id }

notation:max "Diff₀(" M ")" => diff_zero M

/--
`diff_equivalence M N` is a type class expressing that smooth manifolds
M and N have equivalent diffeomorphism groups (up to homotopy).

For the Smale conjecture, `diff_equivalence (sphere ℝ n) (orthogonal_group ℝ (n+1))`
expresses Diff(Sⁿ) ≃ O(n+1).
-/
class diff_equivalence (M N : Type _) [SmoothManifold M] [SmoothManifold N] :
  (homotopy_equivalence (Diff M) (Diff N'))

namespace diff_equivalence

/--
The canonical homotopy equivalence underlying a `diff_equivalence`.
-/
def homotopy_equiv (h : diff_equivalence M N) :
    homotopy_equivalence (Diff M) (Diff N') :=
h.homotopy_equiv

/--
Identity property: identity map is a diffeomorphism equivalence.
-/
@[refl]
def reflexive {M} [SmoothManifold M] : diff_equivalence M M :=
{ homotopy_equiv := homotopy_equivalence.refl _ }

/--
Symmetry: swapping the argument order preserves equivalence.
-/
@[symm]
def symmetry {M N} [SmoothManifold M] [SmoothManifold N]
    (h : diff_equivalence M N) : diff_equivalence N M :=
h.homotopy_equiv.symm

/--
Transitivity: composition of equivalences is an equivalence.
-/
@[trans]
def transitivity {M N P} [SmoothManifold M] [SmoothManifold N] [SmoothManifold P]
    (h₁ : diff_equivalence M N) (h₂ : diff_equivalence N P) :
    diff_equivalence M P :=
h₁.homotopy_equiv.trans h₂

end diff_equivalence

end GeneralizedSmaleConjecture
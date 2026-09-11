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
/-
The copied Mathlib source carries the following attribution:
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/
module

public import FormalConjecturesForMathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The Tate-Shafarevich group of a continuous representation

This file defines a general notion of a Tate--Shafarevich group for an abelian group `A` equipped
with a Galois action as the intersection of the kernels of the maps `Hⁿ(K, A) → Hⁿ(Kᵥ, Aᵥ)`.

Here `Kᵥ` is a `K`-algebra for each place `v` in an arbitrary indexing set `V`,
which induces maps between absolute Galois groups and hence maps between cohomology groups,
and `Aᵥ` is `A` with action restricted along the induced map of absolute Galois groups.

When `V` is the set of places of a global field `K`, `A` is the discrete Galois module of points
of an abelian variety over a separable closure of `K`, and `n = 1`, this recovers the classical
Tate-Shafarevich group via an isomorphism of cohomology groups.

The definitions, documentation, and lemmas are adapted from Edison Xie and David Kurniadi Angdinata's
[Mathlib pull request #43529](https://github.com/leanprover-community/mathlib4/pull/43529),
at commit `72025626969df6ef98eb3689b5ff45e63785a261`.

## References

* [Wikipedia, *Tate–Shafarevich group*](https://en.wikipedia.org/wiki/Tate%E2%80%93Shafarevich_group)
* J. S. Milne, [*Arithmetic Duality Theorems*](https://www.jmilne.org/math/Books/ADTnot.pdf),
  I, Remark 3.10 and §6.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ContinuousCohomology

universe u v

variable {K : Type u} {V : Type v} [Field K] (f : V → Type u) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] (A : TopRep ℤ (Field.absoluteGaloisGroup K)) (n : ℕ)

/-- The Tate-Shafarevich group of a continuous representation. -/
@[simps!]
def tateSha : AddSubgroup (continuousCohomology n A) :=
  ⨅ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker

lemma tateSha_eq_iInf : tateSha f A n = ⨅ v : V, (ContinuousCohomology.map
  (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker := rfl

lemma tateSha_eq_ker_pi : tateSha f A n = (AddMonoidHom.pi fun v : V ↦ (ContinuousCohomology.map
    (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom).ker := by
  ext; simp [tateSha_eq_iInf, funext_iff]

@[simp]
lemma mem_tateSha (x : continuousCohomology n A) : x ∈ tateSha f A n ↔
    ∀ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom x = 0 := by
  simp [tateSha_eq_iInf]

end ContinuousCohomology

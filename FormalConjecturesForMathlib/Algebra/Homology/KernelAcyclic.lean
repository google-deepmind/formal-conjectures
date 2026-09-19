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

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Epimorphisms of complexes with acyclic kernel

An epimorphism of complexes in an abelian category sits in a short exact sequence with its
kernel, so the long exact homology sequence exchanges two conditions on it: being a
quasi-isomorphism, and having acyclic kernel.

One direction holds for an arbitrary complex shape; the converse is stated for nonnegative
cochain complexes, where the degree `n + 1` used to kill the connecting map always exists.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι} {A B : HomologicalComplex C c}

/-- The kernel of an epimorphic quasi-isomorphism of complexes is acyclic. -/
lemma kernel_acyclic_of_epi_of_quasiIso (f : A ⟶ B) [Epi f] [QuasiIso f] :
    (kernel f).Acyclic := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  exact hS.acyclic_X₁ (by dsimp [S]; infer_instance)

/-- An epimorphism of nonnegative cochain complexes with acyclic kernel is a quasi-isomorphism. -/
lemma quasiIso_of_epi_of_kernel_acyclic
    {A B : CochainComplex C ℕ} (f : A ⟶ B) [Epi f]
    (h : (kernel f).Acyclic) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  have hmono : Mono (homologyMap f n) :=
    (hS.homology_exact₂ n).mono_g ((h n).isZero_homology.eq_of_src _ _)
  have hepi : Epi (homologyMap f n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((h (n + 1)).isZero_homology.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi C _ _ _ _ (homologyMap f n) hmono hepi

end HomologicalComplex

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

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normal coordinates from a split derivative

A map with a split injective strict derivative extends to an actual local coordinate map
by adding vectors in the kernel of a left inverse. This is an application of the inverse
function theorem, not an assumed flattening equivalence. The zero-normal slice is exactly
the original parametrization on the constructed coordinate domain. Identifying that slice
with an entire geometric support additionally requires a local embedding assertion.
-/

@[expose] public noncomputable section

open Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- A specified left inverse splits the ambient vector space into the original tangent
space and the actual kernel of that left inverse. -/
def splitKernelEquiv (A : E →L[𝕜] F) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) : (E × P.ker) ≃L[𝕜] F :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => A z.1 + z.2
      invFun := fun y => (P y, ⟨y - A (P y), by
        have hPA : P (A (P y)) = P y := DFunLike.congr_fun h (P y)
        change P (y - A (P y)) = 0
        rw [map_sub, hPA, sub_self]⟩)
      left_inv := by
        intro z
        have hPA : P (A z.1) = z.1 := DFunLike.congr_fun h z.1
        have hz : P (z.2 : F) = 0 := z.2.property
        ext <;> simp [hPA, hz]
      right_inv := by intro y; dsimp; abel
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, map_add,
        Submodule.coe_add]; abel
      map_smul' := by intros; simp }

@[simp] theorem splitKernelEquiv_apply (A : E →L[𝕜] F) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) (z : E × P.ker) :
    A.splitKernelEquiv P h z = A z.1 + z.2 := rfl

@[simp] theorem splitKernelEquiv_symm_fst (A : E →L[𝕜] F) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) (y : F) :
    ((A.splitKernelEquiv P h).symm y).1 = P y := rfl

end ContinuousLinearMap

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {f : E → F} {A : E →L[𝕜] F} {a : E}

local instance splitNormalKernelComplete (P : F →L[𝕜] E) : CompleteSpace P.ker :=
  FiniteDimensional.complete 𝕜 P.ker

omit [CompleteSpace E] in
/-- Adding normal vectors makes the split injective derivative invertible. -/
theorem add_kernel (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) :
    HasStrictFDerivAt (fun z : E × P.ker => f z.1 + z.2)
      (A.splitKernelEquiv P h).toContinuousLinearMap (a, 0) := by
  have h1 := hf.comp (a, (0 : P.ker))
    (ContinuousLinearMap.fst 𝕜 E P.ker).hasStrictFDerivAt
  have h2 := P.ker.subtypeL.hasStrictFDerivAt.comp
    (a, (0 : P.ker)) (ContinuousLinearMap.snd 𝕜 E P.ker).hasStrictFDerivAt
  convert h1.add h2 using 1 <;> rfl

/-- The actual inverse-function-theorem coordinate map `(v,n) ↦ f(v)+n`. -/
def normalChart (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) :
    OpenPartialHomeomorph (E × P.ker) F :=
  (hf.add_kernel P h).toOpenPartialHomeomorph _

@[simp] theorem normalChart_apply (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) (z : E × P.ker) :
    hf.normalChart P h z = f z.1 + z.2 := rfl

/-- The selected point belongs to the coordinate domain. -/
theorem normalChart_mem_source (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) :
    (a, 0) ∈ (hf.normalChart P h).source :=
  (hf.add_kernel P h).mem_toOpenPartialHomeomorph_source

/-- The selected image point belongs to the ambient coordinate neighborhood. -/
theorem normalChart_mem_target (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) :
    f a ∈ (hf.normalChart P h).target := by
  simpa using (hf.normalChart P h).map_source (hf.normalChart_mem_source P h)

/-- Inverse normal coordinates send every parametrized point in the coordinate domain
to precisely its tangent parameter and zero normal coordinate. -/
theorem normalChart_symm_apply (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) (v : E)
    (hv : (v, 0) ∈ (hf.normalChart P h).source) :
    (hf.normalChart P h).symm (f v) = (v, 0) := by
  simpa using (hf.normalChart P h).left_inv hv

/-- On its ambient target, zero normal coordinate is equivalent to membership in the
image of the zero-normal part of the actual coordinate domain. -/
theorem normalChart_normal_eq_zero_iff (hf : HasStrictFDerivAt f A a) (P : F →L[𝕜] E)
    (h : P.comp A = ContinuousLinearMap.id 𝕜 E) (y : F)
    (hy : y ∈ (hf.normalChart P h).target) :
    ((hf.normalChart P h).symm y).2 = 0 ↔
      ∃ v : E, (v, 0) ∈ (hf.normalChart P h).source ∧ f v = y := by
  let e := hf.normalChart P h
  constructor
  · intro hn
    change (e.symm y).2 = 0 at hn
    refine ⟨(e.symm y).1, ?_, ?_⟩
    · simpa only [← hn] using e.map_target hy
    · have hright := e.right_inv hy
      change f (e.symm y).1 + (e.symm y).2 = y at hright
      rw [hn] at hright
      simpa only [Submodule.coe_zero, add_zero] using hright
  · rintro ⟨v, hv, rfl⟩
    rw [hf.normalChart_symm_apply P h v hv]

end HasStrictFDerivAt

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
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

variable {n : ℕ} {ι : Type*}

/-- The set of real points of the affine variety cut out by a family
`S : ι → MvPolynomial (Fin n) ℚ`, viewed inside `ℝⁿ` via base change along `ℚ → ℝ`. -/
def realLocus (S : ι → MvPolynomial (Fin n) ℚ) : Set (Fin n → ℝ) :=
  {x | ∀ i, MvPolynomial.aeval x (S i) = (0 : ℝ)}

/-- The image inside `ℝⁿ` of the set of rational solutions of `S`: the points of `ℝⁿ` whose
coordinates are rational and which satisfy each polynomial in `S`. -/
def rationalImage (S : ι → MvPolynomial (Fin n) ℚ) : Set (Fin n → ℝ) :=
  (fun q : Fin n → ℚ ↦ fun k ↦ ((q k : ℝ))) ''
    {q | ∀ i, MvPolynomial.eval q (S i) = 0}

/-- The image of the rational locus is contained in the real locus: zero loci are compatible
with the base change `ℚ → ℝ`. -/
theorem rationalImage_subset_realLocus (S : ι → MvPolynomial (Fin n) ℚ) :
    rationalImage S ⊆ realLocus S := by
  rintro x ⟨q, hq, rfl⟩
  intro i
  show (MvPolynomial.aeval (fun k ↦ ((q k : ℝ)))) (S i) = 0
  have hcomp : (fun k ↦ ((q k : ℝ))) = (algebraMap ℚ ℝ) ∘ q := by
    funext k; simp
  rw [hcomp, MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_eq_eval, hq i,
    map_zero]

/-- The real locus is closed in `ℝⁿ`: it is a finite intersection of preimages of `{0}` under
continuous polynomial maps. -/
theorem isClosed_realLocus (S : ι → MvPolynomial (Fin n) ℚ) [Finite ι] :
    IsClosed (realLocus S) := by
  have hreal : realLocus S = ⋂ i, {x | MvPolynomial.aeval x (S i) = (0 : ℝ)} := by
    ext x; simp [realLocus]
  rw [hreal]
  cases nonempty_fintype ι
  refine isClosed_iInter (fun i => ?_)
  have hcont : Continuous (fun x : Fin n → ℝ ↦ MvPolynomial.aeval x (S i)) := by
    have : (fun x : Fin n → ℝ ↦ MvPolynomial.aeval x (S i)) =
        (fun x : Fin n → ℝ ↦ MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℝ) (S i))) := by
      funext x
      rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map]
      rfl
    rw [this]
    exact MvPolynomial.continuous_eval _
  exact isClosed_eq hcont continuous_const

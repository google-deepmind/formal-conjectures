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

/-!
# Mathoverflow 235893

*Reference:* [mathoverflow/235893](https://mathoverflow.net/questions/235893)
asked by user [*Willie Wong*](https://mathoverflow.net/users/3948/willie-wong)
-/

open scoped EuclideanGeometry

namespace Mathoverflow235893

variable (n : ℕ)

/-- For topological spaces $X$ and $Y$ we say a function $f : X → Y$ is *connected* is it sends
connected sets to connected sets.
-/
def IsConnectedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ ⦃s : Set X⦄, IsConnected s → IsConnected (f '' s)

/--
By a standard result, every continuous map is connected
-/
@[category test, AMS 54]
theorem Continuous.isConnectedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : IsConnectedMap f :=
  fun _ h ↦ IsConnected.image h f (Continuous.continuousOn hf)

/--
A set in $\mathbb{R}$ is connected if and only if it is order-connected and non-empty.
-/
@[category test, AMS 54]
lemma isConnected_iff_ordConnected_and_nonempty {s : Set ℝ} :
    IsConnected s ↔ s.OrdConnected ∧ s.Nonempty := by
  /-
  We prove this by combining the facts that connected sets in $\mathbb{R}$ are exactly the order-connected sets, and that connected sets are by definition non-empty.
  -/
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2.ordConnected, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1.isPreconnected⟩
/--
If $f : \mathbb{R} \to \mathbb{R}$ is a connected bijection, then its inverse is also a connected bijection.
-/
@[category test, AMS 54]
lemma isConnectedMap_symm_of_R (f : ℝ ≃ ℝ) (hf : IsConnectedMap f) : IsConnectedMap f.symm := by
  /-
  We prove this by contradiction. Suppose the inverse is not connected. Then it maps some connected set to a disconnected set.
  By the characterization of connected sets in $\mathbb{R}$, this means there are points $a, c$ in the image and a point $b$ between them that is not in the image.
  We then use the connectedness of $f$ on the intervals $[a, b]$ and $[b, c]$ to derive a contradiction, as $f(b)$ must be either less than or greater than both $f(a)$ and $f(c)$, which violates the intermediate value property.
  -/
  intro s hs
  rw [isConnected_iff_ordConnected_and_nonempty] at hs ⊢
  rcases hs with ⟨h_ord, h_nonempty⟩
  have h_nonempty' : (f.symm '' s).Nonempty := by
    rcases h_nonempty with ⟨y, hy⟩
    use f.symm y
    exact Set.mem_image_of_mem f.symm hy
  refine ⟨?_, h_nonempty'⟩
  rw [Set.ordConnected_def]
  intro a ha c hc b hb
  rw [Equiv.image_symm_eq_preimage] at ha hc ⊢
  by_contra hfb
  have h_not_mem : f b ∉ Set.uIcc (f a) (f c) := by
    intro h
    cases le_total (f a) (f c) with
    | inl hle =>
      rw [Set.uIcc_of_le hle] at h
      exact hfb (h_ord.out ha hc h)
    | inr hle =>
      rw [Set.uIcc_of_ge hle] at h
      exact hfb (h_ord.out hc ha h)
  have hI1 : IsConnected (Set.Icc a b) := by
    rw [isConnected_iff_ordConnected_and_nonempty]
    exact ⟨Set.ordConnected_Icc, Set.nonempty_Icc.mpr hb.1⟩
  have hI2 : IsConnected (Set.Icc b c) := by
    rw [isConnected_iff_ordConnected_and_nonempty]
    exact ⟨Set.ordConnected_Icc, Set.nonempty_Icc.mpr hb.2⟩
  have hfI1 := hf hI1
  have hfI2 := hf hI2
  rw [isConnected_iff_ordConnected_and_nonempty] at hfI1 hfI2
  have h_uIcc1 : Set.uIcc (f a) (f b) ⊆ f '' Set.Icc a b := by
    apply hfI1.1.uIcc_subset
    · exact Set.mem_image_of_mem f (Set.left_mem_Icc.mpr hb.1)
    · exact Set.mem_image_of_mem f (Set.right_mem_Icc.mpr hb.1)
  have h_uIcc2 : Set.uIcc (f b) (f c) ⊆ f '' Set.Icc b c := by
    apply hfI2.1.uIcc_subset
    · exact Set.mem_image_of_mem f (Set.left_mem_Icc.mpr hb.2)
    · exact Set.mem_image_of_mem f (Set.right_mem_Icc.mpr hb.2)
  have h_cases : f b < min (f a) (f c) ∨ max (f a) (f c) < f b := by
    rw [Set.uIcc, Set.mem_Icc, not_and_or, not_le, not_le] at h_not_mem
    exact h_not_mem
  rcases h_cases with h_lt | h_gt
  · let y := min (f a) (f c)
    have hy1 : y ∈ Set.uIcc (f a) (f b) := by
      rw [Set.uIcc_eq_union, Set.mem_union, Set.mem_Icc, Set.mem_Icc]
      right
      exact ⟨h_lt.le, min_le_left _ _⟩
    have hy2 : y ∈ Set.uIcc (f b) (f c) := by
      rw [Set.uIcc_eq_union, Set.mem_union, Set.mem_Icc, Set.mem_Icc]
      left
      exact ⟨h_lt.le, min_le_right _ _⟩
    have h_x1 : ∃ x1 ∈ Set.Icc a b, f x1 = y := h_uIcc1 hy1
    have h_x2 : ∃ x2 ∈ Set.Icc b c, f x2 = y := h_uIcc2 hy2
    rcases h_x1 with ⟨x1, hx1, hfx1⟩
    rcases h_x2 with ⟨x2, hx2, hfx2⟩
    have h_eq : x1 = x2 := f.injective (hfx1.trans hfx2.symm)
    have h_eq_b : x1 = b := by linarith [hx1.2, hx2.1, h_eq]
    have : f b = min (f a) (f c) := by rw [← h_eq_b, hfx1]
    linarith
  · let y := max (f a) (f c)
    have hy1 : y ∈ Set.uIcc (f a) (f b) := by
      rw [Set.uIcc_eq_union, Set.mem_union, Set.mem_Icc, Set.mem_Icc]
      left
      exact ⟨le_max_left _ _, h_gt.le⟩
    have hy2 : y ∈ Set.uIcc (f b) (f c) := by
      rw [Set.uIcc_eq_union, Set.mem_union, Set.mem_Icc, Set.mem_Icc]
      right
      exact ⟨le_max_right _ _, h_gt.le⟩
    have h_x1 : ∃ x1 ∈ Set.Icc a b, f x1 = y := h_uIcc1 hy1
    have h_x2 : ∃ x2 ∈ Set.Icc b c, f x2 = y := h_uIcc2 hy2
    rcases h_x1 with ⟨x1, hx1, hfx1⟩
    rcases h_x2 with ⟨x2, hx2, hfx2⟩
    have h_eq : x1 = x2 := f.injective (hfx1.trans hfx2.symm)
    have h_eq_b : x1 = b := by linarith [hx1.2, hx2.1, h_eq]
    have : f b = max (f a) (f c) := by rw [← h_eq_b, hfx1]
    linarith
/--
The composition of two connected maps is a connected map.
-/
@[category test, AMS 54]
lemma isConnectedMap_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : IsConnectedMap f) (hg : IsConnectedMap g) :
    IsConnectedMap (g ∘ f) := by
  /-
  We prove this by simply applying the definition of a connected map twice.
  -/
  intro s hs
  rw [Set.image_comp]
  exact hg (hf hs)

/--
A homeomorphism is a connected map.
-/
@[category test, AMS 54]
lemma isConnectedMap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : IsConnectedMap h := by
  /-
  We prove this by noting that a homeomorphism is continuous, and continuous maps preserve connectedness.
  -/
  intro s hs
  exact hs.image h h.continuous.continuousOn

/--
If $f : \mathbb{R}^1 \to \mathbb{R}^1$ is a connected bijection, then its inverse is also a connected bijection.
-/
@[category test, AMS 54]
lemma isConnectedMap_symm_of_E1 (f : ℝ^1 ≃ ℝ^1) (hf : IsConnectedMap f) : IsConnectedMap f.symm := by
  /-
  We prove this by conjugating $f$ with the standard homeomorphism between $\mathbb{R}^1$ and $\mathbb{R}$, and then applying the corresponding result for $\mathbb{R}$.
  -/
  let h : ℝ^1 ≃ₜ ℝ := (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans (Homeomorph.funUnique (Fin 1) ℝ)
  let g : ℝ ≃ ℝ := h.symm.toEquiv.trans (f.trans h.toEquiv)
  have hg_conn : IsConnectedMap g := by
    have h1 : IsConnectedMap h.symm := isConnectedMap_homeomorph h.symm
    have h2 : IsConnectedMap h := isConnectedMap_homeomorph h
    change IsConnectedMap (h ∘ f ∘ h.symm)
    exact isConnectedMap_comp (isConnectedMap_comp h1 hf) h2
  have hg_symm_conn : IsConnectedMap g.symm := isConnectedMap_symm_of_R g hg_conn
  have hf_eq : (f.symm : ℝ^1 → ℝ^1) = h.symm ∘ g.symm ∘ h := by
    ext x
    simp [g]
  rw [hf_eq]
  have h1 : IsConnectedMap h := isConnectedMap_homeomorph h
  have h2 : IsConnectedMap h.symm := isConnectedMap_homeomorph h.symm
  change IsConnectedMap (h.symm ∘ g.symm ∘ h)
  exact isConnectedMap_comp (isConnectedMap_comp h1 hg_symm_conn) h2


/--
Assume for $n>1$, $f:\mathbb{R}^n\to\mathbb{R}^n$ is a bijection, where $\mathbb{R}^n$ is equipped
with the standard topology. Does the connectedness of (the induced power set map) $f$ imply
that of $f^{-1}$?
-/
@[category research open, AMS 26 54]
theorem mathoverflow_235893 :
    answer(sorry) ↔ ∀ n > 1, ∀ (f : ℝ^n ≃ ℝ^n), IsConnectedMap f → IsConnectedMap f.symm := by
  sorry

/--
There exists a connected bijection ℝ → ℝ^2 where the inverse is not connected,
proven in [mathoverflow/260589](https://mathoverflow.net/questions/260589) by user
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen).
-/
@[category research solved, AMS 26 54]
theorem mathoverflow_260589 :
    ∃ f : ℝ ≃ ℝ^2, IsConnectedMap f ∧ ¬ IsConnectedMap f.symm := by
  sorry

-- TODO: Add remarks from the mathoverflow post

end Mathoverflow235893

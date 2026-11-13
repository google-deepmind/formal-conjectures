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

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite prefixes of discrete Markov trajectories

The finite-prefix distribution is defined by iterating PMFs. It agrees with the corresponding
Ionescu–Tulcea trajectory marginal. Thus equality of all finite-prefix distributions determines
an infinite play law. A support-preserving intertwining lift also identifies projected hidden-state
laws, by keeping the joint distribution of the observed prefix and current hidden state.

The trajectory construction follows Mathlib's Ionescu–Tulcea API, based on
O. Kallenberg, *Foundations of Modern Probability*, Theorem 8.24.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DiscreteTrajectory

variable {X : Type*}

/-- A trajectory through time `n`, including time zero. -/
abbrev Prefix (n : ℕ) := Finset.Iic n → X

/-- The last coordinate of a finite prefix. -/
def lastPrefix {n : ℕ} (x : Prefix (X := X) n) : X := x ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- Delete the final coordinate of a nontrivial prefix. -/
def restrictPrefix {n : ℕ} (x : Prefix (X := X) (n + 1)) : Prefix (X := X) n :=
  fun k ↦ x ⟨k, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans (Nat.le_succ n))⟩

/-- Extend a prefix by one coordinate. -/
def appendPrefix {n : ℕ} (x : Prefix (X := X) n) (y : X) : Prefix (X := X) (n + 1) :=
  fun k ↦ if h : (k : ℕ) ≤ n then x ⟨k, Finset.mem_Iic.mpr h⟩ else y

@[simp] lemma last_appendPrefix {n : ℕ} (x : Prefix (X := X) n) (y : X) :
    lastPrefix (appendPrefix x y) = y := by simp [lastPrefix, appendPrefix]

@[simp] lemma restrict_appendPrefix {n : ℕ} (x : Prefix (X := X) n) (y : X) :
    restrictPrefix (appendPrefix x y) = x := by
  funext k
  simp [restrictPrefix, appendPrefix, Finset.mem_Iic.mp k.2]

@[simp] lemma append_restrict_last {n : ℕ} (x : Prefix (X := X) (n + 1)) :
    appendPrefix (restrictPrefix x) (lastPrefix x) = x := by
  funext k
  by_cases hk : (k : ℕ) ≤ n
  · simp [appendPrefix, hk, restrictPrefix]
  · have heq : k = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      exact Nat.le_antisymm (Finset.mem_Iic.mp k.2)
        (Nat.succ_le_of_lt (lt_of_not_ge hk))
    subst k
    simp [appendPrefix, lastPrefix]

lemma appendPrefix_eq_iff {n : ℕ} (x : Prefix (X := X) n) (y : X)
    (z : Prefix (X := X) (n + 1)) :
    appendPrefix x y = z ↔ x = restrictPrefix z ∧ y = lastPrefix z := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact append_restrict_last z

/-- The distribution of the finite prefix, obtained by independently iterating the one-step PMF. -/
noncomputable def prefixPMF (μ : PMF X) (step : X → PMF X) :
    (n : ℕ) → PMF (Prefix (X := X) n)
  | 0 => μ.map (fun x ↦ fun _ ↦ x)
  | n + 1 => (prefixPMF μ step n).bind fun x ↦
      (step (lastPrefix x)).map (appendPrefix x)

open scoped Classical in
lemma map_appendPrefix_apply {n : ℕ} (p : PMF X) (x : Prefix (X := X) n)
    (z : Prefix (X := X) (n + 1)) :
    (p.map (appendPrefix x)) z = if x = restrictPrefix z then p (lastPrefix z) else 0 := by
  simp only [PMF.map_apply, eq_comm (a := z), appendPrefix_eq_iff]
  by_cases hx : x = restrictPrefix z <;> simp [hx]

lemma prefixPMF_succ_apply (μ : PMF X) (step : X → PMF X) (n : ℕ)
    (z : Prefix (X := X) (n + 1)) :
    prefixPMF μ step (n + 1) z = prefixPMF μ step n (restrictPrefix z) *
      step (lastPrefix (restrictPrefix z)) (lastPrefix z) := by
  classical
  rw [prefixPMF, PMF.bind_apply]
  simp_rw [map_appendPrefix_apply]
  simp [mul_ite]

lemma prefixPMF_zero_apply (μ : PMF X) (step : X → PMF X) (z : Prefix (X := X) 0) :
    prefixPMF μ step 0 z = μ (lastPrefix z) := by
  classical
  have heq (x : X) : z = (fun _ ↦ x) ↔ lastPrefix z = x := by
    constructor
    · intro h
      exact congrFun h ⟨0, by simp⟩
    · intro h
      funext k
      have : k = ⟨0, by simp⟩ := Subsingleton.elim _ _
      subst k
      exact h
  simp [prefixPMF, PMF.map_apply, heq]

variable {Y : Type*}

/-- Apply a state observation to each coordinate of a prefix. -/
def mapPrefix (f : X → Y) {n : ℕ} (x : Prefix (X := X) n) : Prefix (X := Y) n :=
  fun k ↦ f (x k)

@[simp] lemma last_mapPrefix (f : X → Y) {n : ℕ} (x : Prefix (X := X) n) :
    lastPrefix (mapPrefix f x) = f (lastPrefix x) := rfl

@[simp] lemma mapPrefix_append (f : X → Y) {n : ℕ} (x : Prefix (X := X) n) (y : X) :
    mapPrefix f (appendPrefix x y) = appendPrefix (mapPrefix f x) (f y) := by
  funext k
  simp only [mapPrefix, appendPrefix]
  split_ifs <;> rfl

private lemma bind_congr_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).mpr ha)]

private lemma map_congr_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  apply bind_congr_support
  intro a ha
  change PMF.pure (f a) = PMF.pure (g a)
  rw [h a ha]

private lemma projection_of_support (f : Y → X) (b : X → PMF Y)
    (hb : ∀ x, (b x).map f = PMF.pure x) {x : X} {y : Y} (hy : y ∈ (b x).support) :
    f y = x := by
  have h : f y ∈ ((b x).map f).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨y, hy, rfl⟩
  rw [hb] at h
  simpa using h

/-- A support invariant for the chain holds at the end of every positive-probability prefix. -/
lemma invariant_lastPrefix (μ : PMF X) (step : X → PMF X) (R : X → Prop)
    (hinit : ∀ x ∈ μ.support, R x)
    (hstep : ∀ x, R x → ∀ y ∈ (step x).support, R y) (n : ℕ)
    (x : Prefix (X := X) n) (hx : x ∈ (prefixPMF μ step n).support) : R (lastPrefix x) := by
  induction n with
  | zero =>
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact hinit a ha
  | succ n ih =>
    obtain ⟨xs, hxs, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    simpa using hstep (lastPrefix xs) (ih xs hxs) a ha

private lemma prefix_joint_succ (μ : PMF Y) (step : Y → PMF Y) (f : Y → X) (n : ℕ) :
    (prefixPMF μ step (n + 1)).map (fun ys ↦ (mapPrefix f ys, lastPrefix ys)) =
      ((prefixPMF μ step n).map (fun ys ↦ (mapPrefix f ys, lastPrefix ys))).bind
        (fun p ↦ (step p.2).map (fun y ↦ (appendPrefix p.1 (f y), y))) := by
  rw [prefixPMF, PMF.map_bind, PMF.bind_map]
  congr 1
  funext xs
  rw [PMF.map_comp]
  congr 1
  funext y
  simp

/-- Intertwining preserves the joint law of the observed prefix and the current hidden state. -/
lemma prefix_joint_of_intertwining (μ : PMF X) (stepX : X → PMF X) (stepY : Y → PMF Y)
    (f : Y → X) (b : X → PMF Y) (R : X → Prop)
    (hb : ∀ x, (b x).map f = PMF.pure x)
    (hinit : ∀ x ∈ μ.support, R x)
    (hstep : ∀ x, R x → ∀ y ∈ (stepX x).support, R y)
    (hint : ∀ x, R x → (b x).bind stepY = (stepX x).bind b) (n : ℕ) :
    (prefixPMF (μ.bind b) stepY n).map (fun ys ↦ (mapPrefix f ys, lastPrefix ys)) =
      (prefixPMF μ stepX n).bind (fun xs ↦ (b (lastPrefix xs)).map (fun y ↦ (xs, y))) := by
  induction n with
  | zero =>
    simp only [prefixPMF, PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_support
    intro x _
    apply map_congr_support
    intro y hy
    have hp := projection_of_support f b hb hy
    apply Prod.ext
    · funext k
      exact hp
    · rfl
  | succ n ih =>
    rw [prefix_joint_succ, ih, PMF.bind_bind, prefixPMF, PMF.bind_bind]
    apply bind_congr_support
    intro xs hxs
    have hR : R (lastPrefix xs) := invariant_lastPrefix μ stepX R hinit hstep n xs hxs
    calc
      ((b (lastPrefix xs)).map (fun y ↦ (xs, y))).bind
          (fun p ↦ (stepY p.2).map (fun y ↦ (appendPrefix p.1 (f y), y))) =
          ((b (lastPrefix xs)).bind stepY).map (fun y ↦ (appendPrefix xs (f y), y)) := by
            simp only [PMF.bind_map, PMF.map_bind, Function.comp_def]
      _ = ((stepX (lastPrefix xs)).bind b).map
          (fun y ↦ (appendPrefix xs (f y), y)) := by rw [hint _ hR]
      _ = (stepX (lastPrefix xs)).bind
          (fun x ↦ (b x).map (fun y ↦ (appendPrefix xs x, y))) := by
            rw [PMF.map_bind]
            apply bind_congr_support
            intro x _
            apply map_congr_support
            intro y hy
            rw [projection_of_support f b hb hy]
      _ = ((stepX (lastPrefix xs)).map (appendPrefix xs)).bind
          (fun zs ↦ (b (lastPrefix zs)).map (fun y ↦ (zs, y))) := by
            simp only [PMF.bind_map, Function.comp_def, last_appendPrefix]

/-- An intertwining lift gives the same finite observed-prefix distribution. -/
lemma prefix_map_of_intertwining (μ : PMF X) (stepX : X → PMF X) (stepY : Y → PMF Y)
    (f : Y → X) (b : X → PMF Y) (R : X → Prop)
    (hb : ∀ x, (b x).map f = PMF.pure x)
    (hinit : ∀ x ∈ μ.support, R x)
    (hstep : ∀ x, R x → ∀ y ∈ (stepX x).support, R y)
    (hint : ∀ x, R x → (b x).bind stepY = (stepX x).bind b) (n : ℕ) :
    (prefixPMF (μ.bind b) stepY n).map (mapPrefix f) = prefixPMF μ stepX n := by
  have h := congrArg (fun p ↦ p.map Prod.fst)
    (prefix_joint_of_intertwining μ stepX stepY f b R hb hinit hstep hint n)
  have hc (xs : Prefix (X := X) n) :
      (b (lastPrefix xs)).map (fun _ ↦ xs) = PMF.pure xs := PMF.map_const _ _
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, hc, PMF.bind_pure] using h

variable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- The kernel of a discrete Markov chain, accepting its finite observed prefix. -/
noncomputable def kernel (step : X → PMF X) (n : ℕ) : Kernel (Prefix (X := X) n) X where
  toFun x := (step (lastPrefix x)).toMeasure
  measurable' := measurable_of_countable _

instance kernel_markov (step : X → PMF X) (n : ℕ) : IsMarkovKernel (kernel step n) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (PMF.toMeasure _); infer_instance

/-- The infinite law constructed from the initial PMF and the successive game kernels. -/
noncomputable def law (μ : PMF X) (step : X → PMF X) : Measure (ℕ → X) :=
  Kernel.trajMeasure μ.toMeasure (kernel step)

instance law_probability (μ : PMF X) (step : X → PMF X) :
    IsProbabilityMeasure (law μ step) := by unfold law; infer_instance

/-- The initial coordinate of the trajectory has the prescribed PMF. -/
lemma map_zero_law (μ : PMF X) (step : X → PMF X) :
    (law μ step).map (fun ω ↦ ω 0) = μ.toMeasure := by
  have heq : (fun ω : ℕ → X ↦ ω 0) =
      (fun x : Prefix (X := X) 0 ↦ x ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold law Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id (μ := μ.toMeasure) using 1
  congr 1

/-- A singleton prefix probability satisfies the same one-step recurrence as the PMF iteration. -/
lemma law_prefix_succ_singleton (μ : PMF X) (step : X → PMF X) (n : ℕ)
    (z : Prefix (X := X) (n + 1)) :
    ((law μ step).map (Preorder.frestrictLe (n + 1))) {z} =
      ((law μ step).map (Preorder.frestrictLe n)) {restrictPrefix z} *
        step (lastPrefix (restrictPrefix z)) (lastPrefix z) := by
  have hevent :
      (Preorder.frestrictLe (n + 1) : (ℕ → X) → _) ⁻¹' {z} =
        (fun ω : ℕ → X ↦ (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹'
          {(restrictPrefix z, lastPrefix z)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      constructor
      · exact congrArg restrictPrefix h
      · exact congrArg lastPrefix h
    · rintro ⟨h₁, h₂⟩
      calc
        Preorder.frestrictLe (n + 1) ω =
            appendPrefix (Preorder.frestrictLe n ω) (ω (n + 1)) :=
          (append_restrict_last (Preorder.frestrictLe (n + 1) ω)).symm
        _ = z := by rw [h₁, h₂]; exact append_restrict_last z
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z), hevent,
    ← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  change ((Kernel.trajMeasure (X := fun _ : ℕ ↦ X) μ.toMeasure (kernel step)).map
    (fun ω ↦ (Preorder.frestrictLe n ω, ω (n + 1)))) _ = _
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
  have hset : ({(restrictPrefix z, lastPrefix z)} : Set (Prefix (X := X) n × X)) =
      {restrictPrefix z} ×ˢ {lastPrefix z} := by ext x; simp
  rw [hset, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton]
  change (step (lastPrefix (restrictPrefix z))).toMeasure {lastPrefix z} * _ = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
  rfl

/-- The finite-dimensional marginal of the actual trajectory is the iterated prefix PMF. -/
lemma map_prefix_law (μ : PMF X) (step : X → PMF X) (n : ℕ) :
    (law μ step).map (Preorder.frestrictLe n) = (prefixPMF μ step n).toMeasure := by
  induction n with
  | zero =>
    have heq : (Preorder.frestrictLe 0 : (ℕ → X) → _) =
        (fun x : X ↦ fun _ : Finset.Iic 0 ↦ x) ∘ (fun ω ↦ ω 0) := by
      funext ω k
      have : k = ⟨0, by simp⟩ := Subsingleton.elim _ _
      subst k
      rfl
    rw [heq, ← Measure.map_map (measurable_of_countable _) (by fun_prop), map_zero_law,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
    rfl
  | succ n ih =>
    apply Measure.ext_of_singleton
    intro z
    rw [law_prefix_succ_singleton, ih,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), prefixPMF_succ_apply]

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
/-- A finite trajectory probability is its initial mass times its transition masses. -/
lemma prefixPMF_apply_frestrictLe (μ : PMF X) (step : X → PMF X) (n : ℕ) (x : ℕ → X) :
    prefixPMF μ step n (Preorder.frestrictLe n x) =
      μ (x 0) * ∏ k ∈ Finset.range n, step (x k) (x (k + 1)) := by
  induction n with
  | zero => simp [prefixPMF_zero_apply, lastPrefix]
  | succ n ih =>
    rw [prefixPMF_succ_apply]
    change prefixPMF μ step n (Preorder.frestrictLe n x) * step (x n) (x (n + 1)) = _
    rw [ih, Finset.prod_range_succ, mul_assoc]

/-- Infinite-law cylinder probabilities are the initial mass times the transition masses. -/
lemma law_cylinder_singleton (μ : PMF X) (step : X → PMF X) (n : ℕ) (x : ℕ → X) :
    ((law μ step).map (Preorder.frestrictLe n)) {Preorder.frestrictLe n x} =
      μ (x 0) * ∏ k ∈ Finset.range n, step (x k) (x (k + 1)) := by
  rw [map_prefix_law, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    prefixPMF_apply_frestrictLe]

/-- Equality of all finite prefix marginals determines an infinite finite measure. -/
lemma eq_of_prefix_marginals {ν₁ ν₂ : Measure (ℕ → X)} [IsFiniteMeasure ν₂]
    (h : ∀ n, ν₁.map (Preorder.frestrictLe n) = ν₂.map (Preorder.frestrictLe n)) : ν₁ = ν₂ := by
  let P (J : Finset ℕ) : Measure (J → X) := ν₂.map J.restrict
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ X) P := by
    intro A B hBA
    dsimp [P]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h₁ : IsProjectiveLimit (α := fun _ : ℕ ↦ X) ν₁ P := (isProjectiveLimit_nat_iff hP ν₁).mpr h
  have h₂ : IsProjectiveLimit (α := fun _ : ℕ ↦ X) ν₂ P := fun _ ↦ rfl
  have (J : Finset ℕ) : IsFiniteMeasure (P J) := by dsimp [P]; infer_instance
  exact h₁.unique h₂

/-- A probability law with the iterated prefix marginals is the actual trajectory law. -/
lemma eq_law_of_prefix_marginals (μ : PMF X) (step : X → PMF X) {ν : Measure (ℕ → X)}
    (h : ∀ n, ν.map (Preorder.frestrictLe n) = (prefixPMF μ step n).toMeasure) :
    ν = law μ step := by
  apply eq_of_prefix_marginals
  intro n
  rw [h, map_prefix_law]

variable [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]

/-- A hidden-state lift satisfying the support-preserving intertwining identity has exactly the
observed infinite play law, including all joint finite-prefix distributions. -/
lemma law_map_of_intertwining (μ : PMF X) (stepX : X → PMF X) (stepY : Y → PMF Y)
    (f : Y → X) (b : X → PMF Y) (R : X → Prop)
    (hb : ∀ x, (b x).map f = PMF.pure x)
    (hinit : ∀ x ∈ μ.support, R x)
    (hstep : ∀ x, R x → ∀ y ∈ (stepX x).support, R y)
    (hint : ∀ x, R x → (b x).bind stepY = (stepX x).bind b) :
    (law (μ.bind b) stepY).map (fun ω n ↦ f (ω n)) = law μ stepX := by
  apply eq_law_of_prefix_marginals
  intro n
  have heq : (Preorder.frestrictLe n : (ℕ → X) → _) ∘ (fun ω k ↦ f (ω k)) =
      mapPrefix f ∘ (Preorder.frestrictLe n : (ℕ → Y) → _) := rfl
  rw [Measure.map_map (by fun_prop) (by fun_prop), heq,
    ← Measure.map_map (measurable_of_countable _) (by fun_prop), map_prefix_law,
    PMF.toMeasure_map _ _ (measurable_of_countable _),
    prefix_map_of_intertwining μ stepX stepY f b R hb hinit hstep hint]

end DiscreteTrajectory

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

public import FormalConjecturesForMathlib.GameTheory.StochasticGame.Equilibrium
public import FormalConjecturesForMathlib.Probability.ProbabilityMassFunction.Observation
public import FormalConjecturesForMathlib.Probability.Kernel.DiscreteTrajectory

/-!
# Clocked finite-memory strategies in stochastic games

A controller uses finite private memory, the public state, and a clock. Its memory update may
randomize after public actions and the next state are observed. Bayesian filtering defines its
behavioral strategy at every feasible public history. The likelihood is that of the controller's
own observed action given the public record. Its canonical strategy is therefore independent of
opponent policies, including at opponent-null histories. Zero own-action likelihood resets the
memory distribution to a designated state.

Reference: Hansen, Ibsen-Jensen and Neyman, *The Big Match with a Clock and a Bit of Memory*,
§2.2 and Theorem 1, https://doi.org/10.1287/moor.2022.1267.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StochasticGame.Game

variable {I S : Type} (G : StochasticGame.Game I S)

/-- A player's finite private-state controller. The clock starts at one. -/
structure MemoryController (i : I) where
  Memory : Type
  memoryFintype : Fintype Memory
  fallback : Memory
  initial : S → PMF Memory
  action : ℕ → (s : S) → Memory → PMF (G.Action i s)
  update : ℕ → (s : S) → Memory → G.JointAction s → S → PMF Memory

attribute [instance] MemoryController.memoryFintype

namespace MemoryController

variable {G} {i : I} (C : G.MemoryController i)

instance : Nonempty C.Memory := ⟨C.fallback⟩

/-- Filter a recorded sequence, using no controller state beyond its private memory. -/
noncomputable def filterPast (t : ℕ) (prior : PMF C.Memory) : List G.Stage → S → PMF C.Memory
  | [], _ => prior
  | x :: xs, s =>
    filterPast (t + 1)
      (PMF.observeUpdate prior (C.action t x.1) (x.2 i) C.fallback
        (fun m ↦ C.update t x.1 m x.2 (RawHistory.initialState G ⟨xs, s⟩))) xs s

private lemma initialState_append (xs : List G.Stage) (x : G.Stage) (s : S) :
    RawHistory.initialState G ⟨xs ++ [x], s⟩ = RawHistory.initialState G ⟨xs, x.1⟩ := by
  cases xs <;> rfl

/-- Appending a public observation performs exactly one Bayesian memory update. -/
theorem filterPast_append (t : ℕ) (prior : PMF C.Memory) (xs : List G.Stage)
    (x : G.Stage) (s : S) :
    C.filterPast t prior (xs ++ [x]) s =
      PMF.observeUpdate (C.filterPast t prior xs x.1) (C.action (t + xs.length) x.1)
        (x.2 i) C.fallback (fun m ↦ C.update (t + xs.length) x.1 m x.2 s) := by
  induction xs generalizing t prior with
  | nil => simp [filterPast, RawHistory.initialState]
  | cons y ys ih =>
    simp only [List.cons_append, filterPast, initialState_append]
    rw [ih]
    simp only [List.length_cons]
    simp only [Nat.add_assoc, Nat.add_comm]

/-- The private-memory distribution before acting at a complete feasible public history. -/
noncomputable def belief (h : G.History) : PMF C.Memory :=
  C.filterPast 1 (C.initial h.initialState) h.past h.current

@[simp] theorem belief_initial (s : S) : C.belief (History.initial s) = C.initial s := rfl

/-- The canonical belief update retains the complete public record. -/
theorem belief_extend (h : G.History) (a : G.JointAction h.current) (s : S)
    (hp : G.transition h.current a s ≠ 0) :
    C.belief (h.extend a s hp) =
      PMF.observeUpdate (C.belief h) (C.action (h.length + 1) h.current)
        (a i) C.fallback (fun m ↦ C.update (h.length + 1) h.current m a s) := by
  simp only [belief, History.initialState_extend, History.past_extend, History.current_extend]
  rw [C.filterPast_append]
  simp [History.length, Nat.add_comm]

/-- The behavioral action law obtained by filtering the controller's private memory. -/
noncomputable def behavior : G.Strategy i :=
  fun h ↦ (C.belief h).bind (C.action (h.length + 1) h.current)

/-- At impossible action observations the final memory distribution is the designated state. -/
theorem belief_extend_of_null (h : G.History) (a : G.JointAction h.current) (s : S)
    (hp : G.transition h.current a s ≠ 0) (hn : C.behavior h (a i) = 0) :
    C.belief (h.extend a s hp) = PMF.pure C.fallback := by
  rw [C.belief_extend]
  exact PMF.observeUpdate_of_mass_eq_zero _ _ _ _ _ hn

/-- Filtering reconstructs the native joint probability of an action and updated memory. -/
theorem belief_extend_reconstruction (h : G.History) (a : G.JointAction h.current) (s : S)
    (hp : G.transition h.current a s ≠ 0) (m' : C.Memory) :
    C.behavior h (a i) * C.belief (h.extend a s hp) m' =
      ∑' m, C.belief h m * C.action (h.length + 1) h.current m (a i) *
        C.update (h.length + 1) h.current m a s m' := by
  rw [C.belief_extend]
  exact PMF.observationMass_mul_observeUpdate _ _ _ _ _ _

/-- The controller's action kernel at fixed private memory. -/
noncomputable def actionStrategy (m : C.Memory) : G.Strategy i :=
  fun h ↦ C.action (h.length + 1) h.current m

/-- Private memory before an action, together with its complete public turn. -/
abbrev NativeTurn := G.Turn × C.Memory

instance [Fintype I] [Fintype S] : Countable C.NativeTurn := inferInstance
instance : MeasurableSpace C.NativeTurn := ⊤
instance : MeasurableSingletonClass C.NativeTurn := ⟨fun _ ↦ trivial⟩

section Native

variable [Fintype I]

/-- Draw the simultaneous public actions with the controller in memory state `m`. -/
noncomputable def nativeAtMemory (σ : G.Profile) (h : G.History) (m : C.Memory) :
    PMF C.NativeTurn :=
  (G.jointPMF (G.revise σ i (C.actionStrategy m)) h).map fun a ↦ (⟨h, a⟩, m)

/-- Draw private memory, then the public action profile. Opponent strategies are unrestricted. -/
noncomputable def nativeSample (σ : G.Profile) (h : G.History) (prior : PMF C.Memory) :
    PMF C.NativeTurn := prior.bind (C.nativeAtMemory σ h)

/-- The independently sampled initial memory and first public action profile. -/
noncomputable def nativeInitial (σ : G.Profile) (s : S) : PMF C.NativeTurn :=
  C.nativeSample σ (History.initial s) (C.initial s)

/-- The native transition samples the public next state, private update, and next actions. -/
noncomputable def nativeNext (σ : G.Profile) (y : C.NativeTurn) : PMF C.NativeTurn :=
  (G.transition y.1.1.current y.1.2).bindOnSupport fun s hs ↦
    (C.update (y.1.1.length + 1) y.1.1.current y.2 y.1.2 s).bind
      (C.nativeAtMemory σ (y.1.1.extend y.1.2 s ((PMF.mem_support_iff _ _).mp hs)))

/-- The private-memory posterior after the current public action has been observed. -/
noncomputable def posterior (x : G.Turn) : PMF C.Memory :=
  PMF.observe (C.belief x.1) (C.action (x.1.length + 1) x.1.current) (x.2 i) C.fallback

/-- Lift a public turn to its conditional private memory. -/
noncomputable def lift (x : G.Turn) : PMF C.NativeTurn :=
  (C.posterior x).map fun m ↦ (x, m)

omit [Fintype I] in
@[simp] theorem lift_map (x : G.Turn) : (C.lift x).map Prod.fst = PMF.pure x := by
  rw [lift, PMF.map_comp]
  exact PMF.map_const _ _

open scoped Classical in
/-- The action-product law separates the controlled player from all opponents. -/
theorem jointPMF_revise_factor (σ : G.Profile) (τ : G.Strategy i) (h : G.History)
    (a : G.JointAction h.current) :
    G.jointPMF (G.revise σ i τ) h a =
      τ h (a i) * ∏ j ∈ Finset.univ.erase i, σ j h (a j) := by
  classical
  rw [G.jointPMF_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), G.revise_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [G.revise_other σ τ (Finset.mem_erase.mp hj).1]

/-- The joint action and memory distribution is the filtered action law times its posterior. -/
theorem nativeActions_factor (σ : G.Profile) (h : G.History)
    (a : G.JointAction h.current) (m : C.Memory) :
    C.belief h m * G.jointPMF (G.revise σ i (C.actionStrategy m)) h a =
      G.jointPMF (G.revise σ i C.behavior) h a * C.posterior ⟨h, a⟩ m := by
  classical
  rw [jointPMF_revise_factor, jointPMF_revise_factor]
  have hb := PMF.observationMass_mul_observe (C.belief h)
    (C.action (h.length + 1) h.current) (a i) C.fallback m
  change C.belief h m * (C.action (h.length + 1) h.current m (a i) * _) = _
  change _ = (C.behavior h (a i) * _) *
    PMF.observe (C.belief h) (C.action (h.length + 1) h.current) (a i) C.fallback m
  rw [← mul_assoc, ← hb]
  simp only [behavior, PMF.observationMass]
  ac_rfl

private theorem bind_pair_of_factor {M A : Type} (p : PMF M) (q : M → PMF A)
    (r : PMF A) (b : A → PMF M) (h : ∀ m a, p m * q m a = r a * b a m) :
    p.bind (fun m ↦ (q m).map fun a ↦ (a, m)) =
      r.bind (fun a ↦ (b a).map fun m ↦ (a, m)) := by
  classical
  ext z
  rcases z with ⟨a, m⟩
  simp only [PMF.bind_apply, PMF.map_apply, Prod.mk.injEq]
  rw [tsum_eq_single m]
  · simp only [and_true, tsum_ite_eq']
    rw [tsum_eq_single a]
    · simpa only [true_and, tsum_ite_eq'] using h m a
    · intro a' ha'
      simp [Ne.symm ha']
  · intro m' hm'
    simp [Ne.symm hm']

/-- Native sampling disintegrates into the public filtered action law and private posterior. -/
theorem nativeSample_eq_lift (σ : G.Profile) (h : G.History) :
    C.nativeSample σ h (C.belief h) =
      (G.initialTurn h (G.revise σ i C.behavior)).bind C.lift := by
  have he := bind_pair_of_factor (C.belief h)
    (fun m ↦ G.jointPMF (G.revise σ i (C.actionStrategy m)) h)
    (G.jointPMF (G.revise σ i C.behavior) h) (fun a ↦ C.posterior ⟨h, a⟩)
    (fun m a ↦ C.nativeActions_factor σ h a m)
  have hm := congrArg
    (PMF.map (fun z : G.JointAction h.current × C.Memory ↦ ((⟨h, z.1⟩ : G.Turn), z.2))) he
  unfold nativeSample nativeAtMemory initialTurn lift
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_map] using hm

private theorem bind_bindOnSupport_comm {A B Z : Type} (p : PMF A) (q : PMF B)
    (f : A → (b : B) → b ∈ q.support → PMF Z) :
    (p.bind fun a ↦ q.bindOnSupport (f a)) =
      q.bindOnSupport (fun b hb ↦ p.bind (fun a ↦ f a b hb)) := by
  simpa only [PMF.bindOnSupport_eq_bind] using
    PMF.bindOnSupport_comm p q (fun a _ b hb ↦ f a b hb)

private theorem bindOnSupport_bind {A B Z : Type} (p : PMF A)
    (f : (a : A) → a ∈ p.support → PMF B) (g : B → PMF Z) :
    (p.bindOnSupport f).bind g = p.bindOnSupport (fun a ha ↦ (f a ha).bind g) := by
  simpa only [PMF.bindOnSupport_eq_bind] using
    PMF.bindOnSupport_bindOnSupport p f (fun b _ ↦ g b)

omit [Fintype I] in
/-- At a possible action observation, the new belief is the posterior followed by the update. -/
theorem belief_extend_of_possible (h : G.History) (a : G.JointAction h.current) (s : S)
    (hp : G.transition h.current a s ≠ 0) (ha : C.behavior h (a i) ≠ 0) :
    C.belief (h.extend a s hp) =
      (C.posterior ⟨h, a⟩).bind (fun m ↦ C.update (h.length + 1) h.current m a s) := by
  rw [C.belief_extend]
  exact PMF.observeUpdate_of_mass_ne_zero _ _ _ _ _ C.fallback ha

/-- The initial native law is the public action law with its private-memory posterior. -/
theorem nativeInitial_eq_lift (σ : G.Profile) (s : S) :
    C.nativeInitial σ s =
      (G.initialTurn (History.initial s) (G.revise σ i C.behavior)).bind C.lift := by
  simpa only [nativeInitial, belief_initial] using C.nativeSample_eq_lift σ (History.initial s)

/-- A possible current observation intertwines the native and filtered public transitions. -/
theorem nativeNext_intertwining (σ : G.Profile) (x : G.Turn)
    (hx : C.behavior x.1 (x.2 i) ≠ 0) :
    (C.lift x).bind (C.nativeNext σ) =
      (G.nextTurn (G.revise σ i C.behavior) x).bind C.lift := by
  simp only [lift, PMF.bind_map, Function.comp_def, nativeNext, nextTurn]
  rw [bind_bindOnSupport_comm, bindOnSupport_bind]
  congr 1
  funext s hs
  refine (PMF.bind_bind (C.posterior x)
    (fun m ↦ C.update (x.1.length + 1) x.1.current m x.2 s)
    (C.nativeAtMemory σ (x.1.extend x.2 s ((PMF.mem_support_iff _ _).mp hs)))).symm.trans ?_
  rw [← C.belief_extend_of_possible x.1 x.2 s ((PMF.mem_support_iff _ _).mp hs) hx]
  exact C.nativeSample_eq_lift σ _

/-- Every public action that is actually sampled has positive own-action likelihood. -/
theorem possible_of_initialTurn_support (σ : G.Profile) (h : G.History) (x : G.Turn)
    (hx : x ∈ (G.initialTurn h (G.revise σ i C.behavior)).support) :
    C.behavior x.1 (x.2 i) ≠ 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  have hh := (PMF.mem_support_iff _ _).mp ha
  rw [jointPMF_revise_factor] at hh
  intro hz
  exact hh (by rw [hz, zero_mul])

/-- Public next-turn kernels preserve the positive-likelihood observation invariant. -/
theorem possible_of_nextTurn_support (σ : G.Profile) (x y : G.Turn)
    (hy : y ∈ (G.nextTurn (G.revise σ i C.behavior) x).support) :
    C.behavior y.1 (y.2 i) ≠ 0 := by
  obtain ⟨s, hs, hy⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp hy
  exact C.possible_of_initialTurn_support σ _ y hy

end Native

section NativeLaw

variable [Fintype I] [Fintype S]

/-- The native private-memory transition kernel, with no behavioral filtering in its definition. -/
noncomputable def nativeKernel (σ : G.Profile) (n : ℕ) :
    Kernel (Finset.Iic n → C.NativeTurn) C.NativeTurn where
  toFun xs := (C.nativeNext σ (xs ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  measurable' := measurable_of_countable _

instance nativeKernel_markov (σ : G.Profile) (n : ℕ) :
    IsMarkovKernel (C.nativeKernel σ n) where
  isProbabilityMeasure xs := by change IsProbabilityMeasure (PMF.toMeasure _); infer_instance

/-- The native continuation law starts with the canonically filtered private memory at `h`. -/
noncomputable def nativeLawFrom (σ : G.Profile) (h : G.History) : Measure (ℕ → C.NativeTurn) :=
  Kernel.trajMeasure (C.nativeSample σ h (C.belief h)).toMeasure (C.nativeKernel σ)

instance nativeLawFrom_probability (σ : G.Profile) (h : G.History) :
    IsProbabilityMeasure (C.nativeLawFrom σ h) := by unfold nativeLawFrom; infer_instance

/-- The actual play law of the private-memory controller against arbitrary behavioral opponents. -/
noncomputable def nativeLaw (σ : G.Profile) (s : S) : Measure (ℕ → C.NativeTurn) :=
  C.nativeLawFrom σ (History.initial s)

instance nativeLaw_probability (σ : G.Profile) (s : S) :
    IsProbabilityMeasure (C.nativeLaw σ s) := C.nativeLawFrom_probability _ _

/-- Filtering realizes the controller's entire public play law against every opponent profile.
The continuation starts at the supplied full history and keeps its absolute clock. -/
theorem nativeLawFrom_map (σ : G.Profile) (h : G.History) :
    (C.nativeLawFrom σ h).map (fun ω t ↦ (ω t).1) =
      G.lawFrom h (G.revise σ i C.behavior) := by
  change (DiscreteTrajectory.law (C.nativeSample σ h (C.belief h)) (C.nativeNext σ)).map
    (fun ω t ↦ (ω t).1) =
      DiscreteTrajectory.law (G.initialTurn h (G.revise σ i C.behavior))
        (G.nextTurn (G.revise σ i C.behavior))
  rw [C.nativeSample_eq_lift]
  exact DiscreteTrajectory.law_map_of_intertwining _ _ _ Prod.fst C.lift
    (fun x ↦ C.behavior x.1 (x.2 i) ≠ 0) C.lift_map
    (C.possible_of_initialTurn_support σ h)
    (fun x _ y hy ↦ C.possible_of_nextTurn_support σ x y hy)
    (C.nativeNext_intertwining σ)

/-- The initial-state controller and its behavioral realization induce the same public play. -/
theorem nativeLaw_map (σ : G.Profile) (s : S) :
    (C.nativeLaw σ s).map (fun ω t ↦ (ω t).1) = G.law s (G.revise σ i C.behavior) :=
  C.nativeLawFrom_map σ (History.initial s)

end NativeLaw

end MemoryController

/-- Every player has a clocked finite-private-memory controller inducing this behavioral profile. -/
def FiniteMemoryRealizable (σ : G.Profile) : Prop :=
  ∀ i, ∃ C : G.MemoryController i, C.behavior = σ i

/-- Realizable profiles have an actual native controller with the same play law against every
opponent profile, from every feasible continuation history. -/
theorem FiniteMemoryRealizable.exists_controller [Fintype I] [Fintype S] {σ : G.Profile}
    (hσ : G.FiniteMemoryRealizable σ) (i : I) :
    ∃ C : G.MemoryController i, C.behavior = σ i ∧ ∀ (ρ : G.Profile) (h : G.History),
      (C.nativeLawFrom ρ h).map (fun ω t ↦ (ω t).1) = G.lawFrom h (G.revise ρ i (σ i)) := by
  obtain ⟨C, hC⟩ := hσ i
  refine ⟨C, hC, ?_⟩
  intro ρ h
  rw [← hC]
  exact C.nativeLawFrom_map ρ h

/-- A clock-dependent Markov strategy uses singleton private memory. -/
noncomputable def markovController (i : I)
    (action : ℕ → (s : S) → PMF (G.Action i s)) : G.MemoryController i where
  Memory := Unit
  memoryFintype := inferInstance
  fallback := ()
  initial _ := PMF.pure ()
  action t s _ := action t s
  update _ _ _ _ _ := PMF.pure ()

@[simp] theorem markovController_behavior (i : I)
    (action : ℕ → (s : S) → PMF (G.Action i s)) (h : G.History) :
    (G.markovController i action).behavior h = action (h.length + 1) h.current := by
  change ((G.markovController i action).belief h).bind (fun _ ↦ _) = _
  exact PMF.bind_const _ _

/-- A stationary strategy is a singleton-memory strategy whose action kernel ignores the clock. -/
noncomputable def stationaryController (i : I)
    (action : (s : S) → PMF (G.Action i s)) : G.MemoryController i :=
  G.markovController i (fun _ ↦ action)

@[simp] theorem stationaryController_behavior (i : I)
    (action : (s : S) → PMF (G.Action i s)) (h : G.History) :
    (G.stationaryController i action).behavior h = action h.current :=
  G.markovController_behavior i (fun _ ↦ action) h

/-- Every profile of clock-dependent Markov strategies belongs to the finite-memory class. -/
theorem finiteMemoryRealizable_markov
    (action : (i : I) → ℕ → (s : S) → PMF (G.Action i s)) :
    G.FiniteMemoryRealizable (fun i h ↦ action i (h.length + 1) h.current) := by
  intro i
  exact ⟨G.markovController i (action i), funext (G.markovController_behavior i (action i))⟩

end StochasticGame.Game

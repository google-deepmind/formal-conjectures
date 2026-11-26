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

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite stochastic games with public histories

A game has finite state-dependent action sets. Behavioral randomization is independent across
players at each public history. Histories record only positive-probability transitions, including
histories assigned probability zero by a strategy profile. The trajectory law is the
Ionescu–Tulcea law of the game kernels, started at a specified history.

References: Solan and Vieille, *Stochastic games* (2015),
https://pmc.ncbi.nlm.nih.gov/articles/PMC4653174/; Flesch and Solan,
*Stochastic games with general payoff functions*, https://arxiv.org/abs/2208.12096.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StochasticGame

/-- A finite-state stochastic game. Each player has nonempty finite actions at each state. -/
structure Game (I S : Type) where
  Action : I → S → Type
  actionFintype : ∀ i s, Fintype (Action i s)
  actionNonempty : ∀ i s, Nonempty (Action i s)
  transition : ∀ s, (∀ i, Action i s) → PMF S
  reward : ∀ (_i : I) (s : S), (∀ j, Action j s) → ℝ

attribute [instance] Game.actionFintype Game.actionNonempty

variable {I S : Type}

namespace Game

variable (G : Game I S)

/-- A simultaneous action profile at a state. -/
abbrev JointAction (s : S) := ∀ i, G.Action i s

/-- A public state and the action profile chosen there. -/
abbrev Stage := Σ s : S, G.JointAction s

/-- A finite public pre-action record, before imposing transition feasibility. -/
structure RawHistory where
  past : List G.Stage
  current : S


instance [Fintype I] [Fintype S] : Countable G.RawHistory := by
  let f : G.RawHistory → List G.Stage × S := fun h ↦ (h.past, h.current)
  exact Function.Injective.countable (f := f) (by
    intro a b h
    cases a
    cases b
    simpa [f] using h)

namespace RawHistory

/-- The first public state, including histories of length zero. -/
def initialState (h : G.RawHistory) : S :=
  match h.past with
  | [] => h.current
  | x :: _ => x.1

/-- Transition feasibility of a public record; chosen actions are legal by their types. -/
def feasiblePast : List G.Stage → S → Prop
  | [], _ => True
  | x :: xs, s => G.transition x.1 x.2 (initialState G ⟨xs, s⟩) ≠ 0 ∧
      feasiblePast xs s

/-- Every recorded transition has positive probability in the game. -/
def Feasible (h : G.RawHistory) : Prop := feasiblePast G h.past h.current

@[simp]
lemma feasible_nil (s : S) : Feasible G ⟨[], s⟩ := trivial

private lemma initialState_append_singleton (xs : List G.Stage) (s s' : S)
    (a : G.JointAction s) :
    initialState G ⟨xs ++ [⟨s, a⟩], s'⟩ = initialState G ⟨xs, s⟩ := by
  cases xs <;> rfl

lemma feasiblePast_append_singleton {xs : List G.Stage} {s s' : S}
    (h : feasiblePast G xs s) (a : G.JointAction s) (hp : G.transition s a s' ≠ 0) :
    feasiblePast G (xs ++ [⟨s, a⟩]) s' := by
  induction xs with
  | nil => exact ⟨hp, trivial⟩
  | cons x xs ih =>
    change G.transition x.1 x.2 (initialState G ⟨xs ++ [⟨s, a⟩], s'⟩) ≠ 0 ∧ _
    rw [initialState_append_singleton]
    exact ⟨h.1, ih h.2⟩

/-- Splitting off the last recorded stage preserves precisely the previous feasibility condition. -/
lemma feasiblePast_append_singleton_iff (xs : List G.Stage) (x : G.Stage) (s' : S) :
    feasiblePast G (xs ++ [x]) s' ↔
      feasiblePast G xs x.1 ∧ G.transition x.1 x.2 s' ≠ 0 := by
  rcases x with ⟨s, a⟩
  induction xs with
  | nil => simp [feasiblePast, initialState]
  | cons y ys ih =>
    cases ys <;> simp_all [feasiblePast, initialState, and_assoc]

end RawHistory

/-- A feasible public pre-action history. No strategy-probability restriction is imposed. -/
abbrev History := {h : G.RawHistory // h.Feasible G}

namespace History

variable {G}

instance : MeasurableSpace G.History := ⊤
instance : MeasurableSingletonClass G.History := ⟨fun _ ↦ trivial⟩

/-- The publicly observed current state. -/
def current (h : G.History) : S := h.1.current

/-- The completed public state-action stages. -/
def past (h : G.History) : List G.Stage := h.1.past

/-- The number of completed stages. The current stage has clock value `length + 1`. -/
def length (h : G.History) : ℕ := h.past.length

/-- The initial publicly observed state. -/
def initialState (h : G.History) : S := h.1.initialState G

/-- The history before the first stage, starting at `s`. -/
def initial (s : S) : G.History := ⟨⟨[], s⟩, trivial⟩

instance [Nonempty S] : Nonempty G.History := ⟨initial (Classical.choice ‹Nonempty S›)⟩

/-- Append the realized actions and a possible next state. -/
def extend (h : G.History) (a : G.JointAction h.current) (s' : S)
    (hp : G.transition h.current a s' ≠ 0) : G.History :=
  ⟨{past := h.past ++ [Sigma.mk h.current a], current := s'}, by
    exact RawHistory.feasiblePast_append_singleton G h.2 a hp⟩

@[simp] lemma current_initial (s : S) : (initial (G := G) s).current = s := rfl
@[simp] lemma past_initial (s : S) : (initial (G := G) s).past = [] := rfl
@[simp] lemma length_initial (s : S) : (initial (G := G) s).length = 0 := rfl
@[simp] lemma initialState_initial (s : S) : (initial (G := G) s).initialState = s := rfl
@[simp] lemma current_extend (h : G.History) (a : G.JointAction h.current) (s') (hp) :
    (h.extend a s' hp).current = s' := rfl
@[simp] lemma past_extend (h : G.History) (a : G.JointAction h.current) (s') (hp) :
    (h.extend a s' hp).past = h.past ++ [⟨h.current, a⟩] := rfl
@[simp] lemma length_extend (h : G.History) (a : G.JointAction h.current) (s') (hp) :
    (h.extend a s' hp).length = h.length + 1 := by simp [length]
@[simp] lemma initialState_extend (h : G.History) (a : G.JointAction h.current) (s') (hp) :
    (h.extend a s' hp).initialState = h.initialState := by
  cases h with
  | mk h hh => cases h with
    | mk xs s => cases xs <;> rfl

/-- Induction over feasible public histories, including all off-path action records. -/
@[elab_as_elim]
lemma induction {motive : G.History → Prop} (h : G.History)
    (init : ∀ s, motive (initial s))
    (step : ∀ (h : G.History) (a : G.JointAction h.current) (s')
      (hp : G.transition h.current a s' ≠ 0), motive h → motive (h.extend a s' hp)) :
    motive h := by
  rcases h with ⟨⟨xs, s⟩, hf⟩
  induction xs using List.reverseRecOn generalizing s with
  | nil => exact init s
  | append_singleton xs x ih =>
    obtain ⟨hprev, hp⟩ := (RawHistory.feasiblePast_append_singleton_iff G xs x s).mp hf
    exact step ⟨⟨xs, x.1⟩, hprev⟩ x.2 s hp (ih x.1 hprev)

end History

/-- A behavioral strategy uses only the public pre-action history. -/
abbrev Strategy (i : I) := (h : G.History) → PMF (G.Action i h.current)

/-- Independent behavioral strategies, one for each player. -/
abbrev Profile := ∀ i, G.Strategy i

instance strategyNonempty (i : I) : Nonempty (G.Strategy i) :=
  ⟨fun h ↦ PMF.pure (Classical.choice (G.actionNonempty i h.current))⟩

instance profileNonempty : Nonempty G.Profile := Pi.instNonempty

/-- A public history together with the actions taken at that history. -/
abbrev Turn := Σ h : G.History, G.JointAction h.current

instance [Fintype I] [Fintype S] : Countable G.Turn :=
  inferInstanceAs (Countable (Sigma _))
instance : MeasurableSpace G.Turn := ⊤
instance : MeasurableSingletonClass G.Turn := ⟨fun _ ↦ trivial⟩

/-- The current state-action stage of a turn; its earlier history does not enter the reward. -/
def Turn.stage (x : G.Turn) : G.Stage := ⟨x.1.current, x.2⟩

/-- Change exactly one player's strategy. Deviations may use arbitrary public histories. -/
noncomputable def revise (σ : G.Profile) (i : I) (τ : G.Strategy i) : G.Profile :=
  by classical exact Function.update σ i τ

@[simp] lemma revise_same (σ : G.Profile) (i : I) (τ : G.Strategy i) :
    G.revise σ i τ i = τ := by classical exact Function.update_self i τ σ

@[simp] lemma revise_other (σ : G.Profile) {i j : I} (τ : G.Strategy i) (h : j ≠ i) :
    G.revise σ i τ j = σ j := by classical exact Function.update_of_ne h τ σ

section Actions

variable [Fintype I]

/-- The product PMF for independent actions at a public history. -/
noncomputable def jointPMF (σ : G.Profile) (h : G.History) : PMF (G.JointAction h.current) :=
  by
    classical
    exact PMF.ofFintype (fun a ↦ ∏ i, σ i h (a i)) (by
      rw [← Fintype.prod_sum]
      have hi (i : I) : ∑ a, σ i h a = 1 := by simpa using (σ i h).tsum_coe
      simp only [hi, Finset.prod_const_one])

@[simp] lemma jointPMF_apply (σ : G.Profile) (h : G.History) (a) :
    G.jointPMF σ h a = ∏ i, σ i h (a i) := rfl

/-- Sample actions at the supplied history. -/
noncomputable def initialTurn (h : G.History) (σ : G.Profile) : PMF G.Turn :=
  (G.jointPMF σ h).map (fun a ↦ ⟨h, a⟩)

/-- Sample a feasible next state, retain the full recorded history, then choose new actions. -/
noncomputable def nextTurn (σ : G.Profile) (x : G.Turn) : PMF G.Turn :=
  (G.transition x.1.current x.2).bindOnSupport fun s' hs' ↦
    G.initialTurn (x.1.extend x.2 s' ((PMF.mem_support_iff _ _).mp hs')) σ

/-- Every turn in the next-step support retains the recorded past and a feasible transition. -/
lemma nextTurn_history_of_mem_support (σ : G.Profile) (x y : G.Turn)
    (hy : y ∈ (G.nextTurn σ x).support) :
    y.1.past = x.1.past ++ [x.stage] ∧
      G.transition x.1.current x.2 y.1.current ≠ 0 ∧
      y.1.length = x.1.length + 1 ∧ y.1.initialState = x.1.initialState := by
  obtain ⟨s', hs', hy⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp hy
  obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  exact ⟨rfl, (PMF.mem_support_iff _ _).mp hs', by simp, by simp⟩

end Actions

variable [Fintype I] [Fintype S]

/-- The one-step law from a complete public record. -/
noncomputable def nextKernel (σ : G.Profile) : Kernel G.Turn G.Turn where
  toFun x := (G.nextTurn σ x).toMeasure
  measurable' := measurable_of_countable _

instance nextKernel_markov (σ : G.Profile) : IsMarkovKernel (G.nextKernel σ) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (PMF.toMeasure _); infer_instance

/-- The next-turn kernel depends on the latest complete public record. -/
noncomputable def turnKernel (σ : G.Profile) (n : ℕ) :
    Kernel (Finset.Iic n → G.Turn) G.Turn where
  toFun x := (G.nextTurn σ (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  measurable' := measurable_of_countable _

instance turnKernel_markov (σ : G.Profile) (n : ℕ) : IsMarkovKernel (G.turnKernel σ n) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (PMF.toMeasure _); infer_instance

/-- The actual infinite play law, including null histories through a fresh start at `h`. -/
noncomputable def lawFrom (h : G.History) (σ : G.Profile) : Measure (ℕ → G.Turn) :=
  Kernel.trajMeasure (G.initialTurn h σ).toMeasure (G.turnKernel σ)

instance lawFrom_probability (h : G.History) (σ : G.Profile) :
    IsProbabilityMeasure (G.lawFrom h σ) := by unfold lawFrom; infer_instance

/-- Equal action-product kernels at every feasible history give the same play law. -/
lemma lawFrom_eq_of_jointPMF_eq (h : G.History) (σ τ : G.Profile)
    (hj : ∀ k, G.jointPMF σ k = G.jointPMF τ k) : G.lawFrom h σ = G.lawFrom h τ := by
  have hi (k : G.History) : G.initialTurn k σ = G.initialTurn k τ := by
    unfold initialTurn
    rw [hj]
  have hn (x : G.Turn) : G.nextTurn σ x = G.nextTurn τ x := by
    unfold nextTurn
    congr 1
    funext s' hs'
    exact hi _
  have hk : G.turnKernel σ = G.turnKernel τ := by
    funext n
    apply Kernel.ext
    intro x
    change (G.nextTurn σ _).toMeasure = (G.nextTurn τ _).toMeasure
    rw [hn]
  unfold lawFrom
  simp only [hi, hk]

/-- The first turn has exactly the initial action-product law at the supplied history. -/
lemma map_zero_lawFrom (h : G.History) (σ : G.Profile) :
    (G.lawFrom h σ).map (fun ω ↦ ω 0) = (G.initialTurn h σ).toMeasure := by
  have heq : (fun ω : ℕ → G.Turn ↦ ω 0) =
      (fun x : Finset.Iic 0 → G.Turn ↦ x ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold lawFrom Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id (μ := (G.initialTurn h σ).toMeasure) using 1
  congr 1

/-- A continuation law starts at its supplied history, even when that history was null before. -/
lemma map_initial_history_lawFrom (h : G.History) (σ : G.Profile) :
    (G.lawFrom h σ).map (fun ω ↦ (ω 0).1) = Measure.dirac h := by
  have heq : (fun ω : ℕ → G.Turn ↦ (ω 0).1) = Sigma.fst ∘ (fun ω ↦ ω 0) := rfl
  rw [heq, ← Measure.map_map (measurable_of_countable _) (by fun_prop),
    G.map_zero_lawFrom, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [initialTurn, PMF.map_comp]
  change ((G.jointPMF σ h).map (Function.const _ h)).toMeasure = Measure.dirac h
  rw [PMF.map_const, PMF.toMeasure_pure]

/-- The second turn follows the game's transition probabilities and the next behavioral actions. -/
lemma map_one_lawFrom (h : G.History) (σ : G.Profile) :
    (G.lawFrom h σ).map (fun ω ↦ ω 1) = G.nextKernel σ ∘ₘ (G.initialTurn h σ).toMeasure := by
  unfold lawFrom Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.map_traj_succ_self,
    ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc]
  congr 1
  rw [Kernel.comp_deterministic_eq_comap]
  ext x
  rfl

/-- The play law from a public initial state. Stage zero in Lean is stage one in the source. -/
noncomputable def law (s : S) (σ : G.Profile) : Measure (ℕ → G.Turn) :=
  G.lawFrom (History.initial s) σ

instance law_probability (s : S) (σ : G.Profile) : IsProbabilityMeasure (G.law s σ) :=
  G.lawFrom_probability _ _

omit [Fintype I] [Fintype S] in
/-- The stage reward as a function of the current turn. -/
def stageReward (i : I) (x : G.Turn) : ℝ := G.reward i x.1.current x.2

lemma measurable_stageReward (i : I) : Measurable (G.stageReward i) :=
  measurable_of_countable _

/-- A common bound on every player's reward in every state and action profile. -/
noncomputable def rewardBound : ℝ := by
  classical
  exact ∑ i : I, ∑ x : G.Stage, ‖G.reward i x.1 x.2‖

lemma rewardBound_nonneg : 0 ≤ G.rewardBound := by
  classical
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))

lemma norm_stageReward_le (i : I) (x : G.Turn) : ‖G.stageReward i x‖ ≤ G.rewardBound := by
  classical
  change ‖G.reward i x.stage.1 x.stage.2‖ ≤ ∑ i : I, ∑ x : G.Stage, ‖G.reward i x.1 x.2‖
  apply le_trans (Finset.single_le_sum (fun j _ ↦ norm_nonneg (G.reward i j.1 j.2))
    (Finset.mem_univ x.stage))
  exact Finset.single_le_sum (f := fun j : I ↦ ∑ z : G.Stage, ‖G.reward j z.1 z.2‖)
    (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)) (Finset.mem_univ i)

end Game
end StochasticGame

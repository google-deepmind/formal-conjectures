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

public import FormalConjecturesUtil

/-!
# Connectivity by short rotations under switching costs

In §3 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask for a probabilistic analogue of classical stable matching
rotations. The question below specifies a balanced market and asks whether cyclic reassignments
that move a small fraction of the firms can connect its stable matchings.
-/

@[expose] public section

open Filter MeasureTheory SwitchingCostMatching
open scoped Topology

namespace ShortRotationConnectivity

/-- In a balanced market a matching is a permutation of the workers. -/
abbrev PerfectMatching (n : ℕ) := Equiv.Perm (Fin n)

/-- Two matchings are adjacent when they differ by one nontrivial cycle that moves at most $L$
firms. -/
def rotationGraph (n : ℕ) (L : ℝ) : SimpleGraph (PerfectMatching n) where
  Adj M N := (M⁻¹ * N).IsCycle ∧ ((M⁻¹ * N).support.card : ℝ) ≤ L
  symm := by
    constructor
    intro M N h
    have hRev : (M⁻¹ * N)⁻¹ = N⁻¹ * M := by simp [mul_inv_rev]
    rw [← hRev]
    exact ⟨h.1.inv, by simpa only [Equiv.Perm.support_inv] using h.2⟩
  loopless := by
    constructor
    intro M h
    simpa using h.1

open scoped Classical in
/-- The matchings that are stable in the given profile at cost $\varepsilon$. -/
noncomputable def stableMatchings {n : ℕ} (p : Profile n n) (ε : ℝ) :
    Finset (PerfectMatching n) :=
  Finset.univ.filter (fun M ↦ IsStable p ε M.toEmbedding)

/-- The profiles for which the graph of stable matchings is connected using cycles of length at
most $L$. -/
def connectivityEvent (n : ℕ) (L ε : ℝ) : Set (Profile n n) :=
  {p | ((rotationGraph n L).induce (stableMatchings p ε : Set (PerfectMatching n))).Connected}

/-- The set of stable matchings is measurable as a function of the profile. -/
@[category API, AMS 60]
theorem measurable_stableMatchings (n : ℕ) (ε : ℝ) :
    Measurable (fun p : Profile n n ↦ stableMatchings p ε) := by
  rw [measurable_finset_iff]
  intro M
  simp only [stableMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold IsStable IsBlockingPair
  fun_prop (disch := exact measurable_pi_apply _)

/-- The connectivity event is measurable under the law of random profiles. -/
@[category API, AMS 60]
theorem measurableSet_connectivityEvent (n : ℕ) (L ε : ℝ) :
    MeasurableSet (connectivityEvent n L ε) := by
  apply Measurable.setOf
  exact (Measurable.of_discrete (f := fun s : Finset (PerfectMatching n) ↦
    ((rotationGraph n L).induce (s : Set (PerfectMatching n))).Connected)).comp
    (measurable_stableMatchings n ε)

/-- The probability that the stable matchings form a connected graph under the cycle length
bound. -/
noncomputable def connectivityProbability (n : ℕ) (L ε : ℝ) : ℝ :=
  (profileMeasureWithWorkers n n).real (connectivityEvent n L ε)

/-- In a balanced market with independent rate-one exponential utilities, set
$\varepsilon_n = \log n/(6\sqrt n)$. For every fixed $\delta>0$, does the probability tend to one
that all $\varepsilon_n$-stable matchings are connected by single-cycle reassignments moving at
most $\delta n$ firms per step, with every intermediate matching $\varepsilon_n$-stable? The
limit uses positive market sizes $n = k+1$. -/
@[category research open, question, AMS 5 60]
theorem shortRotationConnectivity :
    ∀ δ : ℝ, 0 < δ → Tendsto
      (fun k : ℕ ↦
        let n := k + 1
        connectivityProbability n (δ * (n : ℝ)) (Real.log n / (6 * Real.sqrt n)))
      atTop (𝓝 1) := by
  sorry

end ShortRotationConnectivity

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

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Instances.AddCircle.Defs

@[expose] public section

open scoped Topology

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed on
an interval `[a, b]` if for every subinterval `[c, d]` of `[a, b]` we have
`lim_{n→ ∞} |{s_1, ..., s_n} ∩ [c, d]| / n = (d - c)/(b-a)`
-/
def IsEquidistributed (a b : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ c d, c ≤ d → Set.Icc c d ⊆ Set.Icc a b →
  Filter.atTop.Tendsto (fun n => ((Finset.range n).filter
    fun m => s m ∈ Set.Icc c d).card / (n : ℝ)) (𝓝 <| (d - c) / (b - a))

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed
modulo 1 or uniformly distributed modulo 1 if the sequence of the fractional parts of
`a_n`, denoted by `(a_n)` or by `a_n − ⌊a_n⌋`, is equidistributed in the interval `[0, 1]`.
-/
def IsEquidistributedModuloOne (s : ℕ → ℝ) : Prop :=
  IsEquidistributed 0 1 (fun n => Int.fract (s n))

/-- A sequence that is equidistributed modulo 1 is dense modulo 1. -/
theorem IsEquidistributedModuloOne.dense_range {s : ℕ → ℝ} (h : IsEquidistributedModuloOne s) :
    Dense (Set.range fun n => (s n : AddCircle (1 : ℝ))) := by
  have key (y : ℝ) : ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) = y := by
    rw [QuotientAddGroup.eq]
    exact ⟨⌊y⌋, by simp [← Int.self_sub_floor]⟩
  rw [dense_iff_inter_open]
  rintro U hU ⟨p, hp⟩
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective p
  set t := Int.fract q
  have hpt : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ U := (key q).symm ▸ hp
  have hpre : IsOpen ((↑) ⁻¹' U : Set ℝ) := hU.preimage (AddCircle.continuous_mk' 1)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre t hpt
  set d := min (t + ε / 2) 1
  have htd : t < d := lt_min (by linarith) (Int.fract_lt_one q)
  have hlim := h t d htd.le (Set.Icc_subset_Icc (Int.fract_nonneg q) (min_le_right _ _))
  have hpos : (0 : ℝ) < (d - t) / (1 - 0) := by simpa using htd
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hpos)).exists
  obtain ⟨m, hm⟩ : ((Finset.range n).filter fun m => Int.fract (s m) ∈ Set.Icc t d).Nonempty :=
    Finset.card_pos.1 <| Nat.pos_of_ne_zero fun h0 => by
      simp only [h0, Nat.cast_zero, zero_div, lt_irrefl] at hn
  obtain ⟨-, hm⟩ := Finset.mem_filter.1 hm
  refine ⟨_, ?_, m, rfl⟩
  have hmem : Int.fract (s m) ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hm.1, hm.2, min_le_left (t + ε / 2) 1]
  simpa [key] using hball hmem

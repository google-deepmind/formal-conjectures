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
# Erdős Problem 139

*Reference:* [erdosproblems.com/139](https://www.erdosproblems.com/139)
-/

open Classical
open scoped Topology

instance {M : Type*} [AddMonoid M] : Inhabited M where
  default := 0


section

variable {M : Type*}

def IsArithmeticProgression [Add M] (l : List M) : Prop :=
  ∃ step, l.Chain' fun s t ↦ t = s + step

namespace IsArithmeticProgression

noncomputable def step [Add M]
    {l : List M} (hl : IsArithmeticProgression l) : M :=
  hl.choose

@[category API, AMS 5 11]
lemma step_def [Add M] {l : List M} (hl : IsArithmeticProgression l) :
    hl.step = hl.choose := rfl

@[category API, AMS 5 11]
lemma step_unique [AddCancelMonoid M] {l : List M} (hl : IsArithmeticProgression l)
    (hl' : 1 < l.length) (u : M) (hu : l.Chain' fun s t ↦ t = s + u) :
    u = hl.step := by
  apply add_left_cancel
  rw [←(List.chain'_iff_get.mp hu) 0 (by omega), hl.step_def,
    ←(List.chain'_iff_get.mp hl.choose_spec) 0 (by omega)]

--For some reason the `Inhabited` instance on `M` doesn't exist!
@[category API, AMS 5 11]
lemma step_zero [AddMonoid M] [Inhabited M] {l : List M}
    (hl : IsArithmeticProgression l) (hl' : hl.step = 0) :
    l = List.replicate l.length l.headI := by
  sorry

end IsArithmeticProgression

section

variable [AddMonoid M]

@[simp, category API, AMS 5 11]
lemma IsArithmeticProgression_nil : IsArithmeticProgression ([] : List M) := by
  use 0; trivial

@[category API, AMS 5 11]
lemma IsArithmeticProgression_singleton (a : M) :
    IsArithmeticProgression [a] := by
  use 0, List.chain'_singleton a

end

@[category API, AMS 5 11]
lemma IsArithmeticProgression_map_range [AddCommMonoid M] (a b : M) (n : ℕ) :
    IsArithmeticProgression <| List.range n |>.map fun i => a + i • b := by
  obtain ⟨-, rfl⟩ := (Nat.eq_zero_or_pos n)
  · simp
  by_cases hn : n = 0
  · omega
  · exact ⟨b, by simp [hn, List.chain'_iff_get, add_assoc, add_smul, one_smul]⟩

@[category API, AMS 5 11]
lemma IsArithmeticProgression_pair [AddCommGroup M] (a b : M) :
    IsArithmeticProgression [a, b] := by
  use b - a ; aesop

variable [AddCommMonoid M]

/--
Say a set `A` is a *`k`-non-arithmetic subset* if it contains non non-trivial
arithmetic progressions of length `k`.
-/
def NonArithmeticSubset (k : ℕ) (A : Set M) : Prop :=
    ∀ (AP : List M) (hAP : IsArithmeticProgression AP),
    AP.length = k → {x | x ∈ (AP : List M)} ⊆ (A : Set M) →
    hAP.step = 0

/--Denote by $r_k(N)$ the size of the largest k-non-arithmetic subset of ${1,...,N}$-/
noncomputable abbrev r (k : ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc (1 : ℤ) N).powerset.filter fun S => NonArithmeticSubset k S.toSet).sup Finset.card

/--
**Erdős Problem 139**:
Let $r_k(N)$ be the size of the largest subset of ${1,...,N}$ which does not contain a non-trivial
$k$-step arithmetic progression. Prove that $r_k(N) = o(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_139 (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) := by
  sorry

/-
TODO(lezeau):
1 - add the various known bounds as variants.
2 - we could consider making some unified "Mathlib"-ready API for Arithmetic progressions since
  these appear in various settings (and other Erdős problems!). Ideally, this should allow for
  possibly infinite indexing types, so let's deal with that can of worms later.
-/

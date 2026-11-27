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
# Written on the Wall II - Conjecture 369

*References:*
- [E. DeLaViña, Written on the Wall II, Conjecture 369](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)
- [Written on the Wall II, Definitions 45, 94 and 110](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json)
- [Counterexample with an independent Lean 4 verification](https://github.com/adamben04/graffiti-pc-369-counterexample)

The 29-vertex counterexample has total domination number $6$, one modal degree, and first-zero
step $6$. The proposed lower bound is $7$. Its construction was inspired by Pepper and Waller's
counterexample to Conjecture 368, shown in [Figure 5 of the 2009 preprint](https://math1um.github.io/Research/r05.pdf).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture369

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of distinct degrees of maximum frequency, counting a unique mode as one. -/
def degreeModeCount : ℕ :=
  let ds := G.degreeMultiset
  let degrees := ds.toFinset
  (degrees.filter fun d => ds.count d = degrees.sup ds.count).card

/-- The number of Havel–Hakimi reductions until the descending degree sequence first contains
a zero. -/
noncomputable def havelHakimiFirstZero : ℕ :=
  sInf {i | 0 ∈ havelHakimiStep^[i] (G.degreeMultiset.sort (· ≥ ·))}

/-- The following claim of Conjecture 369 is false: every tree $T$ on $n > 2$ vertices satisfies
$\gamma_t(T) \ge \mathrm{dd}_{\mathrm{mode}}(T) + (n \bmod 2)k$, where $\gamma_t$ is the total
domination number, $\mathrm{dd}_{\mathrm{mode}}$ counts the distinct modal degrees, and $k$ is
the first Havel–Hakimi step at which a zero appears. -/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/adamben04/graffiti-pc-369-counterexample/blob/656cf0ba8bc8bd8290ba1a7753b0cbe1b860f967/Graffiti369.lean"]
theorem conjecture369 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree → 2 < Fintype.card V →
        degreeModeCount T + (Fintype.card V % 2) * havelHakimiFirstZero T ≤
          T.totalDominationNumber := by
  sorry

private abbrev pathOnFour : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 3)}

/-- The four-vertex path has two modal degrees and its first reduction gives $[1, 1, 0]$. -/
@[category test, AMS 5]
example : degreeModeCount pathOnFour = 2 ∧ havelHakimiFirstZero pathOnFour = 1 := by
  let s : Set ℕ := {i | 0 ∈ havelHakimiStep^[i] (pathOnFour.degreeMultiset.sort (· ≥ ·))}
  have hd : pathOnFour.degreeMultiset = ([2, 2, 1, 1] : List ℕ) := by decide
  have hsorted : pathOnFour.degreeMultiset.sort (· ≥ ·) = [2, 2, 1, 1] := by
    rw [hd, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ (by decide)
  have h0 : 0 ∉ s := by
    change 0 ∉ havelHakimiStep^[0] _
    rw [hsorted, Function.iterate_zero_apply]
    decide
  have h1 : 1 ∈ s := by
    change 0 ∈ havelHakimiStep^[1] _
    rw [hsorted, Function.iterate_succ_apply, Function.iterate_zero_apply]
    change 0 ∈ ([1, 0, 1] : List ℕ).mergeSort (· ≥ ·)
    exact (List.mergeSort_perm _ _).mem_iff.mpr (by decide)
  refine ⟨by decide, IsLeast.csInf_eq ⟨h1, fun i hi => ?_⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr fun h => h0 (h ▸ hi)

end WrittenOnTheWallII.GraphConjecture369

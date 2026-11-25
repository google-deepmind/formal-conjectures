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

public import FormalConjecturesForMathlib.Combinatorics.StableMarriage
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Function.Iterate

/-!
# Deferred acceptance with complete strict preferences

A deterministic implementation of men-proposing deferred acceptance. At each step the first
unmatched man with an untried candidate proposes. There are at most $n^2$ proposals.

Reference: D. Gale and L. S. Shapley, *College Admissions and the Stability of Marriage*
(1962), https://doi.org/10.2307/2312726.
-/

@[expose] public section

namespace StableMarriage

/-- The proposal counters and the tentative partner held by each woman. -/
structure ProposalState (n : ℕ) where
  /-- Number of proposals already made by each man. -/
  next : Fin n → ℕ
  /-- Man whose proposal each woman currently holds. -/
  held : Fin n → Option (Fin n)

/-- One proposal, or no change if every man is matched or has exhausted his list. -/
def proposalStep {n : ℕ} (p : Profile n) (s : ProposalState n) : ProposalState n :=
  match (List.finRange n).find? (fun m ↦ s.next m < n ∧ ∀ w, s.held w ≠ some m) with
  | none => s
  | some m =>
    if h : s.next m < n then
      let w := (p.manRank m).symm ⟨s.next m, h⟩
      let accept := match s.held w with
        | none => true
        | some old => decide (p.womanRank w m < p.womanRank w old)
      ⟨Function.update s.next m (s.next m + 1),
        if accept then Function.update s.held w (some m) else s.held⟩
    else s

/-- The terminal state of men-proposing deferred acceptance, after $n^2$ possible proposals. -/
def deferredAcceptance {n : ℕ} (p : Profile n) : ProposalState n :=
  (proposalStep p)^[n * n] ⟨fun _ ↦ 0, fun _ ↦ none⟩

/-- The total number of proposals in men-proposing deferred acceptance. -/
def numProposals {n : ℕ} (p : Profile n) : ℕ :=
  ∑ m, (deferredAcceptance p).next m

/-- In the empty market no proposal is made. -/
theorem numProposals_zero (p : Profile 0) : numProposals p = 0 := by
  simp [numProposals]

/-- In the singleton market exactly one proposal is made. -/
theorem numProposals_one : numProposals (default : Profile 1) = 1 := by
  decide

/-- For two men, averaging over their four ranking profiles gives five halves proposals,
regardless of the women's rankings. -/
theorem proposal_sum_two :
    ∀ Q : Fin 2 → Equiv.Perm (Fin 2),
      ∑ P : Fin 2 → Equiv.Perm (Fin 2), numProposals ⟨P, Q⟩ = 10 := by
  decide

end StableMarriage

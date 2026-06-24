/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Nat Finset List

/--
A237271: Number of parts in the symmetric representation of $\sigma(n)$.
a(n) is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is $1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$, which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

def sorted_divisors_list (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num_2_dense_sublists (n : ℕ) : ℕ :=
  let divs_list := sorted_divisors_list n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
-- You can put your definitions and lemmas here.
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : a n = num_2_dense_sublists n := by
  -- EVOLVE-BLOCK-START
  rw [←eq_comm, a,num_2_dense_sublists]
  push_cast[sorted_divisors_list, two_mul,List.countP_eq_length_filter, add_left_cancel_iff,.≥.,.>·]
  rw [←List.ofFn_get ↑(.zip _ _)]
  norm_num [ ← two_mul,←List.toFinset_card_of_nodup ((List.nodup_finRange @_).filter _),List.ofFn_eq_map,List.filter_map]
  refine ((congr_arg _)).comp Finset.filter_congr fun and x => ⟨fun S => ⟨Nat.not_even_iff_odd.mp (mt (·.two_dvd) ? _), S.le⟩, fun and => and.2.lt_of_ne (and.1.elim (by valid))⟩
  use fun⟨A, B⟩=>absurd (n.divisors.sort_sorted (.≤.)) fun and' =>((List.get_of_mem (( Finset.mem_sort (.≤.)).mpr (Nat.mem_divisors.2 ⟨show A ∣(n) from(? _),?_⟩))).elim) ?_
  · exact (dvd_of_mul_left_dvd (B▸Nat.mem_divisors.1 (( Finset.mem_sort _).mp ↑(List.getElem_mem _) ) ).1)
  · use (by cases.▸and.pos)
  · exact (fun R M=>B.not_lt (lt_of_le_of_lt (and'.rel_get_of_le ((monotone_iff_forall_lt.2 (List.pairwise_iff_get.1 and')).reflect_lt (M▸Nat.lt_of_mul_lt_mul_left (B▸S)))) (by linarith)))
  -- EVOLVE-BLOCK-END

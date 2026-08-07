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

import FormalConjectures.Util.ProblemImports

open Nat List Finset

/--
A229232: Number of undirected circular permutations $\pi(1), \ldots, \pi(n)$ of $1, \ldots, n$
with the $n$ numbers $\pi(1)\pi(2)-1, \pi(2)\pi(3)-1, \ldots, \pi(n)\pi(1)-1$ all prime.
This is defined by counting the total number of linear permutations satisfying the property, and dividing by $2n$,
as is standard for counting equivalence classes under the dihedral group action on a set of size $n$.
-/
noncomputable def A229232 (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    -- The list of numbers [1, 2, ..., n]
    let l_n : List ℕ := (List.range N).map Nat.succ

    -- The set of all linear permutations of {1, ..., n}.
    let all_perms : Finset (List ℕ) := l_n.permutations.toFinset

    -- Predicate to check if a list satisfies the cyclic prime product minus one property.
    let is_cyclic_prime_chain (p : List ℕ) : Prop :=
      -- rotate (N-1) performs a left rotation by 1, giving the next cyclic element.
      let l_cyclic := p.rotate (N - 1)
      -- zip pairs (a_i, a_{i+1}) cyclically.
      (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))

    -- Filter the permutations based on the decidable prime chain property.
    let good_perms : Finset (List ℕ) :=
      all_perms.filter fun p => decide (is_cyclic_prime_chain p)

    -- The result is the total count of good linear permutations divided by $2n$.
    good_perms.card / (2 * N)

/--
Conjecture: a(n) > 0 for all n > 5 with n not equal to 13.
-/
theorem oeis_a229232_conjecture_gt_zero (n : ℕ) :
  (n > 5 ∧ n ≠ 13) → A229232 n > 0 := by
  sorry

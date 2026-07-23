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

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S


theorem a_one : A232616 1 = 1 := by
  delta A232616
  delta A232616_prop
  fapply Nat.isLeast_find ⟨1,by decide⟩|>.csInf_eq

theorem a_two : A232616 2 = 2 := by
  norm_num[A232616]
  delta A232616_prop
  apply Nat.isLeast_find ⟨2,by decide⟩ |>.csInf_eq

theorem a_three : A232616 3 = 4 := by
  norm_num [A232616]
  delta A232616_prop
  apply(Nat.isLeast_find ⟨4,by decide⟩).csInf_eq

theorem a_four : A232616 4 = 5 := by
  norm_num [ A232616]
  delta and A232616_prop
  apply(Nat.isLeast_find ⟨5,by decide⟩).csInf_eq

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

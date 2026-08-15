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

open Nat Classical

/--
Riesel problem: let $k=2n-1$; then $a(n)=$smallest $m \ge 1$ such that $k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.
We use PNat for the exponent $m$ to correctly model $m \ge 1$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let k : ℕ := 2 * n - 1
    -- The predicate P(m) for m in PNat (m >= 1).
    let P (m : PNat) : Prop := (k * (2 ^ (m : ℕ)) - 1).Prime

    -- Use classical choice to find the minimum, or return -1 if no such prime exists.
    dite (∃ m : PNat, P m)
    (fun h_exists : ∃ m : PNat, P m =>
      -- PNat.find returns the minimum element. We coerce it to ℕ, then to ℤ.
      let m_min := PNat.find h_exists
      (m_min : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )


theorem a_one : a 1 = 2 := by
  simp_all[a]
  rw_mod_cast[dif_pos (by exists@2),PNat.find_eq_iff]
  refine ⟨by decide,fun R L => match R with|(1)=>by decide⟩

theorem a_two : a 2 = 1 := by
  delta a
  norm_num[Exists.intro (1 : ℕ+),PNat.find_eq_iff]

theorem a_three : a 3 = 2 := by
  norm_num[a ·]
  use if a:_ then(dif_pos a▸mod_cast(PNat.find_eq_iff _).2 ((.symm @?_)))else a.elim<|by exists@2
  exists(fun a s=>match a with|1=>by decide)

theorem a_four : a 4 = 1 := by
  delta and a
  norm_num[Exists.intro (1 : ℕ+),PNat.find_eq_iff]


/--
It is conjectured that the integer k = 509203 is the smallest Riesel number,
that is, the first n such that a(n) = -1 is 254602.
-/
theorem oeis_a108129_conjecture_0 :
  a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) :=
by sorry

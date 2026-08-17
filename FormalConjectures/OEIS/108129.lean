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

import FormalConjecturesUtil

/-!
# Riesel Problem

Riesel problem: let $k=2n-1$; then $a(n)$ is the smallest $m \ge 1$ such that
$k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.

*References:*
- [A108129](https://oeis.org/A108129)
-/

namespace OeisA108129

open Nat

open Classical in
/-- The primary defining sequence `a`.
Riesel problem: let $k=2n-1$; then $a(n)$ is the smallest $m \ge 1$ such that
$k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.
We use PNat for the exponent $m$ to correctly model $m \ge 1$. -/
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
      let mMin := PNat.find h_exists
      (mMin : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )

/-- `PNat.find` does not reduce, so read off `a n` from the characterisation of the minimum
instead of evaluating it. -/
@[category API, AMS 11]
private lemma a_eq (n : ℕ) (hn : n ≠ 0) (m : ℕ) (hm0 : 0 < m)
    (hm : ((2 * n - 1) * 2 ^ m - 1).Prime)
    (hmin : ∀ l, 0 < l → l < m → ¬((2 * n - 1) * 2 ^ l - 1).Prime) :
    a n = m := by
  have hex : ∃ l : ℕ+, ((2 * n - 1) * 2 ^ (l : ℕ) - 1).Prime := ⟨⟨m, hm0⟩, hm⟩
  have hfind : PNat.find hex = ⟨m, hm0⟩ :=
    (PNat.find_eq_iff hex).2 ⟨hm, fun l hl => hmin l l.pos hl⟩
  delta a
  rw [if_neg hn, dif_pos hex, hfind]
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2 :=
  a_eq 1 (by norm_num) 2 (by norm_num) (by decide)
    fun l h0 h2 => by obtain rfl : l = 1 := by omega
                      decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 :=
  a_eq 2 (by norm_num) 1 (by norm_num) (by decide) fun l h0 h1 => by omega

@[category test, AMS 11]
theorem a_3 : a 3 = 2 :=
  a_eq 3 (by norm_num) 2 (by norm_num) (by decide)
    fun l h0 h2 => by obtain rfl : l = 1 := by omega
                      decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 :=
  a_eq 4 (by norm_num) 1 (by norm_num) (by decide) fun l h0 h1 => by omega

/--
It is conjectured that the integer $k = 509203$ is the smallest Riesel number,
that is, the first $n$ such that $a(n) = -1$ is $254602$.
-/
@[category research open, AMS 11]
theorem conjecture :
  a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) :=
by sorry

end OeisA108129

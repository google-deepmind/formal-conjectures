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

namespace OeisA000041

/-
Name: "No powers as partition numbers"

There are no partition numbers $p(k)$ of the form $x^m$, with $x,m$ integers $>1$.

*Reference*: [OEIS A000041](https://oeis.org/A000041)
-/

def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

def IsPerfectPower (n : ℕ) : Prop :=
    ∃ x m : ℕ, 1 < x ∧ 1 < m ∧ x ^ m = n
/--
There are no partition numbers $p(k)$ of the form $x^m$, with $x,m$ integers $>1$.
See comment by Zhi-Wei Sun (Dec 02 2013).
-/
@[category research open, AMS 11]
theorem noPowerPartitionNumber (k : ℕ) : answer(sorry) ↔ ¬IsPerfectPower (p k) := by
    sorry

end OeisA000041

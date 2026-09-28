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
# Erdős Problem 140

*References:*
- [erdosproblems.com/140](https://www.erdosproblems.com/140)
- [KeMe23] Kelley, Zander and Meka, Raghu, *Strong bounds for 3-progressions*. 2023 IEEE 64th
  Annual Symposium on Foundations of Computer Science (FOCS) (2023).
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos140

/--
$r_3(N)$ is the size of the largest subset of $\{1, \dots, N\}$ which does not contain a
non-trivial $3$-term arithmetic progression.

Here `addRothNumber s` is the largest cardinality of a `ThreeAPFree` subset of the finset `s`,
where a set $A$ is `ThreeAPFree` iff whenever $a, b, c \in A$ with $a + c = b + b$ we have $a = b$.
-/
def r3 (N : ℕ) : ℕ := addRothNumber (Finset.Icc 1 N)

/-- Sanity check: $r_3(N)$ coincides with Mathlib's `rothNumberNat N`, which uses
$\{0, \dots, N - 1\}$ instead of $\{1, \dots, N\}$. -/
@[category test, AMS 5 11]
theorem r3_eq_rothNumberNat (N : ℕ) : r3 N = rothNumberNat N := by
  have h : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [r3, h, addRothNumber_Ico]
  simp

/--
Let $r_3(N)$ be the size of the largest subset of $\{1, \dots, N\}$ which does not contain a
non-trivial $3$-term arithmetic progression. Prove that $r_3(N) \ll N / (\log N)^C$ for every
$C > 0$.

Proved by Kelley and Meka [KeMe23].
-/
@[category research solved, AMS 5 11]
theorem erdos_140 (C : ℝ) (hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) / Real.log N ^ C) := by
  sorry

end Erdos140

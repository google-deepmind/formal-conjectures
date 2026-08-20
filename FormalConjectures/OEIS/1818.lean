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
# Squares of double factorials

Squares of double factorials: $a(n) = ((2n-1)!!)^2 = (1 \cdot 3 \cdot 5 \cdots (2n-1))^2$.

*References:*
- [A001818](https://oeis.org/A001818)
-/

namespace OeisA1818

/-- The sequence of squares of double factorials: $a(n) = ((2n-1)!!)^2$. -/
def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (2 * k + 1)) ^ 2

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 225 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 11025 := by decide

/-- Characteristic function $f(j, k)$ for matrix entries in $\mathbb{Z}/p^2\mathbb{Z}$. -/
noncomputable def fEntry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    let iInt : ℤ := i
    let jInt : ℤ := j
    let num : R := (iInt + jInt : ℤ)
    let den : R := (iInt - jInt : ℤ)
    num * den⁻¹

/--
Conjecture 1: For any primitive $2n$-th root $\zeta$ of unity, the permanent of the $2n \times 2n$
matrix $[m(j,k)]_{j,k=1..2n}$ coincides with $a(n) = ((2n-1)!!)^2$, where $m(j,k)$ is
$(1+\zeta^{j-k})/(1-\zeta^{j-k})$ if $j \neq k$, and $1$ otherwise.
- Zhi-Wei Sun, Dec 21 2021
-/
@[category research open, AMS 11 15]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ) := by
  sorry

/--
Conjecture 2: Let $p$ be an odd prime. Then the permanent of the $(p-1) \times (p-1)$ matrix
$[f(j,k)]_{j,k=1..p-1}$ is congruent to $a((p-1)/2) = ((p-2)!!)^2 \pmod{p^2}$,
where $f(j,k)$ is $(j+k)/(j-k)$ if $j \neq k$, and $f(j,k) = 1$ otherwise.
- Zhi-Wei Sun, Dec 22 2021
-/
@[category research open, AMS 11 15]
theorem conjecture2 {p : ℕ} (hp : p.Prime) (h_odd : p ≠ 2) :
    let N : ℕ := p - 1
    let R := ZMod (p ^ 2)
    let Idx := Fin N
    let M : Matrix Idx Idx R := fun i j => fEntry (i.val + 1) (j.val + 1)
    (M.permanent : R) = (a ((p - 1) / 2) : R) := by
  sorry

end OeisA1818

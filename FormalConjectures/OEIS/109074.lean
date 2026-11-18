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
# Numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$

The sequence $a(n)$ is the numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$.
The OEIS entry records the conjecture that this ratio equals $\text{A005156}(n) / \text{A005156}(n-1)$,
where $\text{A005156}(n)$ is the number of $(2n+1) \times (2n+1)$ vertically symmetric alternating
sign matrices (VSASMs). This follows from Robbins's VSASM product formula, proved by Kuperberg
(2002).

*References:*
- [A109074](https://oeis.org/A109074)
- [A005156](https://oeis.org/A005156)
- G. Kuperberg, "Symmetry classes of alternating-sign matrices under one roof,"
  [arXiv:math/0008184](https://arxiv.org/abs/math/0008184), *Ann. of Math.* **156** (2002),
  835–866.
-/

@[expose] public section

namespace OeisA109074

open Nat

/--
The rational number defined by $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$,
whose numerator is A109074.
-/
def frac (n : ℕ) : ℚ :=
  let numTerm : ℕ := (6 * n - 2).choose (2 * n)
  let denTerm : ℕ := 2 * ((4 * n - 1).choose (2 * n))
  (numTerm : ℚ) / (denTerm : ℚ)

/--
The primary defining sequence `a`.
$a(n)$ is the numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$.
-/
def a (n : ℕ) : ℕ :=
  (frac n).num.natAbs

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 26 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 323 := by native_decide

/--
Lists of length `k` with entries in `{-1, 0, 1}`.
-/
def trinaryLists : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 =>
    (trinaryLists k).flatMap fun xs => [(-1 : ℤ) :: xs, 0 :: xs, 1 :: xs]

/--
Checks that all prefix sums of `xs` starting from `acc` lie in `{0, 1}` and the final sum is `1`.
-/
def isAsmLineAux : ℤ → List ℤ → Bool
  | acc, [] => acc == 1
  | acc, x :: xs =>
    let s := acc + x
    (s == 0 || s == 1) && isAsmLineAux s xs

/--
A list of integers in `{-1, 0, 1}` is a valid alternating sign matrix row/column if all of its
prefix sums lie in `{0, 1}` and its total sum is `1`.
-/
def isAsmLine (xs : List ℤ) : Bool :=
  isAsmLineAux 0 xs

/--
All vertically symmetric alternating sign matrix rows of length `2 * n + 1`.
-/
def symAsmRows (n : ℕ) : List (List ℤ) :=
  (trinaryLists n).flatMap fun half =>
    [(-1 : ℤ), 0, 1].filterMap fun mid =>
      let row := half ++ [mid] ++ half.reverse
      if isAsmLine row then some row else none

/--
Number of ways to complete `k` remaining vertically symmetric ASM rows given the current column
partial sums `colSums`.
-/
def countVsasmRows (rows : List (List ℤ)) : ℕ → List ℤ → ℕ
  | 0, colSums => if colSums.all (· == 1) then 1 else 0
  | k + 1, colSums =>
    let step := countVsasmRows rows k
    rows.foldl (fun acc r =>
      let nextSums := List.zipWith (· + ·) colSums r
      if nextSums.all (fun s => s == 0 || s == 1) then
        acc + step nextSums
      else acc) 0

/--
A005156 (offset 0): the number of $(2n+1) \times (2n+1)$ alternating sign matrices symmetric
about the vertical axis (VSASMs).
-/
def b (n : ℕ) : ℕ :=
  countVsasmRows (symAsmRows n) (2 * n + 1) (List.replicate (2 * n + 1) 0)

@[category test, AMS 5 11]
theorem b_0 : b 0 = 1 := by decide

@[category test, AMS 5 11]
theorem b_1 : b 1 = 1 := by decide

@[category test, AMS 5 11]
theorem b_2 : b 2 = 3 := by decide

@[category test, AMS 5 11]
theorem b_3 : b 3 = 26 := by decide

@[category test, AMS 5 11]
theorem b_4 : b 4 = 646 := by native_decide

/--
"It is conjectured that $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right) =
\text{A005156}(n+1)/\text{A005156}(n)$."

The OEIS comment indexes A005156 from $1$; for the $0$-indexed sequence `b` this states
`frac (n + 1) = b (n + 1) / b n`. This holds by the product formula
$$\text{A005156}(n) = \frac{1}{2^n} \prod_{k=1}^{n} \frac{(6k-2)!\,(2k-1)!}{(4k-1)!\,(4k-2)!}$$
conjectured by Robbins and proved by Kuperberg (2002).
-/
@[category research solved, AMS 5 11]
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) := by
  sorry

end OeisA109074

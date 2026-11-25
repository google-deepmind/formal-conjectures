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
# Even bases with a unique cycle of the four-digit Kaprekar map

*Reference:* [arxiv/2606.20439](https://arxiv.org/abs/2606.20439)
**Four-digit Kaprekar dynamics in odd bases**
by *Evan Chen, Ken Ono, Richard E. Schwartz, Dinesh S. Thakur*,
J. Integer Seq. 29 (2026), Article 26.4.7.

In base $B$, take a four-digit word (leading zeros allowed), arrange its digits in
decreasing and in increasing order, and subtract the second number from the first. A cycle is
the orbit of a periodic word whose digits are not all equal, counted up to cyclic shift. Fixed
points have least period $1$. Base ten has one cycle, the fixed point $6174$.

Remark 28 of the source records, from numerical evidence, which even bases have exactly one
cycle: $B = 3 \cdot 2^{2k+1}$, $B = 5 \cdot 2^{2k+1}$ and $B = 7 \cdot 2^{3n \pm 1}$. This was
proved, with the least periods $6(k+1)$, $1$ and $3$, in Corollary 2 of
R. Galyavin, *Cycles of the four-digit Kaprekar map in even bases* (2026),
[doi:10.5281/zenodo.24358739](https://doi.org/10.5281/zenodo.24358739).

The definitions below are those of the Challenge file of the linked Palomar entry, so the
registered proof proves exactly these statements.
-/

@[expose] public section

namespace Arxiv.«2606.20439»

/-- The four base-`B` digits of `x`, most significant first, leading zeros allowed. For
$x < B^4$ they are the unique $d_0, d_1, d_2, d_3 < B$ with
$x = d_0 B^3 + d_1 B^2 + d_2 B + d_3$. -/
def digits4 (B x : Nat) : List Nat :=
  [x / B / B / B % B, x / B / B % B, x / B % B, x % B]

/-- Read a list of digits, most significant first, as a base-`B` number (Horner's rule). -/
def ofDigits (B : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * B + d) 0

/-- Insert `a` into a list sorted in decreasing order, keeping it sorted. -/
def insertDesc (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if b ≤ a then a :: b :: l else b :: insertDesc a l

/-- Insertion sort into decreasing order. -/
def sortDesc : List Nat → List Nat
  | [] => []
  | a :: l => insertDesc a (sortDesc l)

/-- The four-digit Kaprekar map $K_B$: the digits of `x` arranged in decreasing order, minus the
same digits arranged in increasing order, both read as base-`B` numbers. -/
def kaprekar (B x : Nat) : Nat :=
  ofDigits B (sortDesc (digits4 B x)) - ofDigits B (sortDesc (digits4 B x)).reverse

/-- In base ten, the Kaprekar map fixes $6174$. -/
@[category test, AMS 11 37]
theorem kaprekar_ten_6174 : kaprekar 10 6174 = 6174 := by decide

/-- `iterate f n x` applies `f` to `x` exactly `n` times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- The four base-`B` digits of `x` are all equal. -/
def IsRepdigit (B x : Nat) : Prop :=
  x / B / B / B % B = x / B / B % B ∧ x / B / B % B = x / B % B ∧ x / B % B = x % B

/-- `x` is a periodic point of $K_B$: some positive number of steps returns to `x`. -/
def IsPeriodic (B x : Nat) : Prop :=
  ∃ k, 0 < k ∧ iterate (kaprekar B) k x = x

/-- `x` has least period `L` under $K_B$, so its cycle has length `L`. -/
def HasPeriod (B x L : Nat) : Prop :=
  0 < L ∧ iterate (kaprekar B) L x = x ∧
    ∀ i, 0 < i → i < L → iterate (kaprekar B) i x ≠ x

/-- $K_B$ has exactly one cycle, of least period `L`: some $x < B^4$ whose digits are not all
equal has least period `L`, and its orbit contains every periodic $y < B^4$ whose digits are
not all equal. -/
def HasUniqueCycleOfLength (B L : Nat) : Prop :=
  ∃ x, x < B ^ 4 ∧ ¬ IsRepdigit B x ∧ HasPeriod B x L ∧
    ∀ y, y < B ^ 4 → ¬ IsRepdigit B y → IsPeriodic B y →
      ∃ j, iterate (kaprekar B) j x = y

/-- Remark 28 of the source: an even base $B \ge 2$ has exactly one four-digit Kaprekar cycle if
and only if $B = 3 \cdot 2^{2k+1}$ or $B = 5 \cdot 2^{2k+1}$ for some $k \ge 0$, or
$B = 7 \cdot 2^n$ with $n \ge 1$ and $3 \nmid n$. -/
@[category research solved, AMS 11 37, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-21-000001&version=1"]
theorem unique_cycle_iff (B : Nat) (hB : 2 ≤ B) (heven : B % 2 = 0) :
    (∃ L, HasUniqueCycleOfLength B L) ↔
      (∃ k, B = 3 * 2 ^ (2 * k + 1)) ∨ (∃ k, B = 5 * 2 ^ (2 * k + 1)) ∨
        (∃ n, 1 ≤ n ∧ ¬ 3 ∣ n ∧ B = 7 * 2 ^ n) := by
  sorry

/-- The lengths of the unique cycles: $6(k+1)$ in base $3 \cdot 2^{2k+1}$, $1$ in base
$5 \cdot 2^{2k+1}$, and $3$ in base $7 \cdot 2^n$ when $n \ge 1$ and $3 \nmid n$. -/
@[category research solved, AMS 11 37, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-21-000001&version=1"]
theorem unique_cycle_length (k n : Nat) :
    HasUniqueCycleOfLength (3 * 2 ^ (2 * k + 1)) (6 * (k + 1)) ∧
      HasUniqueCycleOfLength (5 * 2 ^ (2 * k + 1)) 1 ∧
      (1 ≤ n → ¬ 3 ∣ n → HasUniqueCycleOfLength (7 * 2 ^ n) 3) := by
  sorry

end Arxiv.«2606.20439»

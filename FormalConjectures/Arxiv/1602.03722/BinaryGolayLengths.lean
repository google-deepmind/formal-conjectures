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
# Binary Golay pair lengths

A binary Golay pair consists of two equal-length sequences with entries $\pm 1$ whose
nontrivial aperiodic autocorrelations cancel. Such pairs are known at every length
$2^a 10^b 26^c$, where $a,b,c$ are nonnegative integers. The open question asks whether
any other positive length occurs.

*References:*
* K.-U. Schmidt, [Sequences with small correlation](https://doi.org/10.1007/s10623-015-0154-7),
  *Designs, Codes and Cryptography* **78** (2016), 237–267, Question 5.2.4.
* [Author's text](https://arxiv.org/abs/1602.03722)
* [OEIS A036975](https://oeis.org/A036975)
-/

@[expose] public section

namespace Arxiv.«1602.03722»

/-- The aperiodic autocorrelation at lag $k$. -/
def aperiodicAutocorrelation (a : List ℤ) (k : ℕ) : ℤ :=
  (List.zipWith (· * ·) a (a.drop k)).sum

/-- A binary sequence has entries in $\{-1,1\}$. -/
def IsBinarySequence (a : List ℤ) : Prop :=
  ∀ x ∈ a, x = 1 ∨ x = -1

/-- A positive-length binary pair whose autocorrelations cancel at every nonzero lag. -/
def IsBinaryGolayPair (a b : List ℤ) : Prop :=
  0 < a.length ∧ a.length = b.length ∧ IsBinarySequence a ∧ IsBinarySequence b ∧
    ∀ k ∈ Finset.Ico 1 a.length,
      aperiodicAutocorrelation a k + aperiodicAutocorrelation b k = 0

instance (a b : List ℤ) : Decidable (IsBinaryGolayPair a b) := by
  unfold IsBinaryGolayPair IsBinarySequence
  infer_instance

/-- The multiplicative family of known binary Golay pair lengths. -/
def KnownLength (n : ℕ) : Prop :=
  ∃ a b c : ℕ, n = 2 ^ a * 10 ^ b * 26 ^ c

@[category test, AMS 5 94]
theorem pair_length_one : IsBinaryGolayPair [1] [1] := by decide

@[category test, AMS 5 94]
theorem pair_length_two : IsBinaryGolayPair [1, 1] [1, -1] := by decide

@[category test, AMS 5 94]
theorem pair_length_four : IsBinaryGolayPair [1, 1, 1, -1] [1, 1, -1, 1] := by decide

@[category test, AMS 5 94]
theorem constant_pair_not_golay : ¬ IsBinaryGolayPair [1, 1] [1, 1] := by decide

@[category test, AMS 5 94]
theorem zero_entry_not_binary : ¬ IsBinaryGolayPair [1, 0] [1, 0] := by decide

@[category test, AMS 5 94]
theorem unequal_lengths_not_golay : ¬ IsBinaryGolayPair [1] [1, -1] := by decide

@[category test, AMS 5 94]
theorem empty_pair_not_golay : ¬ IsBinaryGolayPair [] [] := by decide

/-- At lag zero the autocorrelation is the length, rather than zero. -/
@[category API, AMS 5 94]
theorem autocorrelation_zero (a : List ℤ) (ha : IsBinarySequence a) :
    aperiodicAutocorrelation a 0 = (a.length : ℤ) := by
  induction a with
  | nil => simp [aperiodicAutocorrelation]
  | cons x xs ih =>
    have hx := ha x (by simp)
    have hxs : IsBinarySequence xs := by
      intro y hy
      exact ha y (by simp [hy])
    have hxx : x * x = 1 := by
      rcases hx with hx | hx <;> simp [hx]
    calc
      aperiodicAutocorrelation (x :: xs) 0 = x * x + aperiodicAutocorrelation xs 0 := by
        simp only [aperiodicAutocorrelation, List.drop_zero, List.zipWith_cons_cons, List.sum_cons]
      _ = ((x :: xs).length : ℤ) := by
        rw [hxx, ih hxs]
        simp [add_comm]

@[category test, AMS 5 94]
theorem known_length_one : KnownLength 1 := by
  exact ⟨0, 0, 0, by norm_num⟩

@[category test, AMS 5 94]
theorem known_length_ten : KnownLength 10 := by
  exact ⟨0, 1, 0, by norm_num⟩

@[category test, AMS 5 94]
theorem known_length_twenty_six : KnownLength 26 := by
  exact ⟨0, 0, 1, by norm_num⟩

/--
Is there a binary Golay pair whose length is outside the family $2^a10^b26^c$?
This is Question 5.2.4 of Schmidt's survey.
-/
@[category research open, question, AMS 5 94]
theorem binary_golay_other_lengths :
    ∃ a b : List ℤ, IsBinaryGolayPair a b ∧ ¬ KnownLength a.length := by
  sorry

end Arxiv.«1602.03722»

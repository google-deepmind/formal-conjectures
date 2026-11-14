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
/-

The definitions `I`, `J`, `Admissible`, `Guarantees`, and `scoreBound`
are copied verbatim (up to docstrings, attributes, and formatting) from
`788/lean/Erdos788/Definitions.lean` in the repository `ShouqiaoW/erdos`
at commit `f2ae0edb45cbdb257e135d51ef855f64caeb348b`
(https://github.com/ShouqiaoW/erdos/blob/f2ae0edb45cbdb257e135d51ef855f64caeb348b/788/lean/Erdos788/Definitions.lean).

Our natural-number-valued definition `f` is obtained by renaming
Shouqiao's `fNat`. The separate integer-valued function `f` and the
definition `IntegerGuarantees` from Shouqiao are not used here.

The lemmas `f_guarantees` and `le_f` correspond to Shouqiao's
`fNat_guarantees` and `le_fNat`, respectively. The statements of lemmas
`guarantees_zero` and `guarantees_le_scoreBound` are copied,
but the proofs are modified.

The lemma `isGreatest_f` gives the natural-number analogue of
Shouqiao's `f_isGreatestIntegerGuarantee`.

The auxiliary lemmas `f_le_card_I` and `admissible_singleton`,
the four finite examples `admissible_repeated_summand`,
`not_admissible_distinct_sum`, `not_admissible_endpoint`, and
`endpoint_notMem_J`, and the small-value results `f_zero`,
`f_one`, `f_two`, and `f_three` do not appear in the cited
`Definitions.lean` and are not covered by the preceding
copied-from attribution.

The source file is unchanged at commit
`d28713ac8245ca86a686b8c67370a8d19d81b242` ("Add MIT license"),
where the repository carries the following license in its file `LICENSE`:

MIT License

Copyright (c) 2026 Shouqiao Wang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 788

*References:*
- [erdosproblems.com/788](https://www.erdosproblems.com/788)
- [Forum thread for problem 788](https://www.erdosproblems.com/forum/thread/788)
- [AlPh25] N. Alon and H. T. Pham, *Random Cayley graphs and random subsets*.
  [arXiv:2509.02561](https://arxiv.org/abs/2509.02561) (2025).
- [BSS00] Baltz, Andreas and Schoen, Tomasz and Srivastav, Anand, *Probabilistic construction of
  small strongly sum-free sets via large Sidon sets*. Colloq. Math. (2000), 171--176.
- [Ch71] Choi, S. L. G., *On a combinatorial problem in number theory*.
  Proc. London Math. Soc. (3) (1971), 629-642.
- [ShouqiaoW/erdos, `Definitions.lean` at `f2ae0ed`]
(https://github.com/ShouqiaoW/erdos/blob/f2ae0edb45cbdb257e135d51ef855f64caeb348b/788/lean/Erdos788/Definitions.lean)
-/

/-
This file formalizes only the statement of the upper-bound question in Erdős Problem 788.
It does not prove the upper bound or formalize the lower bound.
-/

@[expose] public section

namespace Erdos788

/-- The possible elements of `C`: the natural numbers strictly between $n$ and $2n$. -/
def I (n : ℕ) : Finset ℕ := Finset.Ioo n (2 * n)

/-- The possible elements of `B`: the natural numbers strictly between $2n$ and $4n$. -/
def J (n : ℕ) : Finset ℕ := Finset.Ioo (2 * n) (4 * n)

/-- We say `B C` is admissible if `C ⊆ I n`,
and no sum of two distinct elements of `C` belongs to `B`. -/
def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧
    ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

/-- Every `B ⊆ J n` has an admissible `C` with $|B|+|C| \geq t$. -/
def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

/-- A uniform upper bound on $|B|+|C|$ of any pair `B ⊆ J n`,
`C ⊆ I n`. -/
def scoreBound (n : ℕ) : ℕ := (J n).card + (I n).card

/-- The largest natural-number threshold `t ≤ scoreBound n` with `Guarantees n t`. -/
noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

/-- The threshold `0` is guaranteed, with `C = ∅`. This is the base case that
`Nat.findGreatest_spec` needs in `f_guarantees`. -/
@[category API, AMS 5 11]
theorem guarantees_zero (n : ℕ) : Guarantees n 0 :=
  fun _ _ => ⟨∅, by simp [Admissible], by simp⟩

/-- Every guaranteed threshold is at most `scoreBound n`, by taking `B = J n`. This shows that
the search bound in `f` does not truncate the maximum. -/
@[category API, AMS 5 11]
theorem guarantees_le_scoreBound {n t : ℕ} (h : Guarantees n t) : t ≤ scoreBound n := by
  obtain ⟨C, hC, ht⟩ := h (J n) subset_rfl
  exact ht.trans (Nat.add_le_add_left (Finset.card_le_card hC.1) _)

/-- `f n` is a guaranteed threshold. -/
@[category API, AMS 5 11]
theorem f_guarantees (n : ℕ) : Guarantees n (f n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (guarantees_zero n)

/-- Every guaranteed natural-number threshold is at most `f n`. -/
@[category API, AMS 5 11]
theorem le_f {n t : ℕ} (h : Guarantees n t) : t ≤ f n := by
  classical
  exact Nat.le_findGreatest (guarantees_le_scoreBound h) h

/-- Taking `B = ∅` shows `f n ≤ |I n|`. -/
@[category API, AMS 5 11]
theorem f_le_card_I (n : ℕ) : f n ≤ (I n).card := by
  obtain ⟨C, hC, h⟩ := f_guarantees n ∅ (Finset.empty_subset _)
  simpa using h.trans (Nat.add_le_add_left (Finset.card_le_card hC.1) _)

/-- A singleton `{c}` with `c ∈ I n` is admissible for every `B`, because only sums of two
distinct elements are constrained. -/
@[category API, AMS 5 11]
theorem admissible_singleton {n c : ℕ} (hc : c ∈ I n) (B : Finset ℕ) : Admissible n B {c} :=
  ⟨by simpa using hc, by simp⟩


/-- Characterization of `f` as the greatest guaranteed threshold. -/
@[category API, AMS 5 11]
theorem isGreatest_f (n : ℕ) :
    IsGreatest {t : ℕ | Guarantees n t} (f n) :=
  ⟨f_guarantees n, fun _ ht => le_f ht⟩

/-- Positive example: `B = {8} ⊆ J 3`, and `C = {4}` is admissible although $4 + 4 = 8 \in B$.
Repeated summands are not constrained. -/
@[category test, AMS 5 11]
theorem admissible_repeated_summand : ({8} : Finset ℕ) ⊆ J 3 ∧ Admissible 3 {8} {4} := by
  unfold Admissible
  decide

/-- Negative example: `B = {9} ⊆ J 3`, and `C = {4, 5}` is not admissible because
$4 + 5 = 9 \in B$ with $4 \neq 5$. -/
@[category test, AMS 5 11]
theorem not_admissible_distinct_sum :
    ({9} : Finset ℕ) ⊆ J 3 ∧ ¬ Admissible 3 {9} {4, 5} := by
  unfold Admissible
  decide

/-- Neither endpoint of $(3, 6)$ can be an element of an admissible `C`, even for `B = ∅`. -/
@[category test, AMS 5 11]
theorem not_admissible_endpoint : ¬ Admissible 3 ∅ {3} ∧ ¬ Admissible 3 ∅ {6} := by
  unfold Admissible
  decide

/-- Neither endpoint of $(6, 12)$ is an allowed element of `B` for `n = 3`. -/
@[category test, AMS 5 11]
theorem endpoint_notMem_J : (6 : ℕ) ∉ J 3 ∧ (12 : ℕ) ∉ J 3 := by
  decide

/-- `I 0 = ∅`, so `f 0 = 0`. -/
@[category test, AMS 5 11]
theorem f_zero : f 0 = 0 := by
  simpa [f, I] using f_le_card_I 0

/-- `I 1 = ∅`, so `f 1 = 0`, although `B = {3}` alone would give score `1`. -/
@[category test, AMS 5 11]
theorem f_one : f 1 = 0 := by
  simpa [f, I] using f_le_card_I 1

/-- `I 2 = {3}`, and `C = {3}` is admissible for every `B`, so `f 2 = 1`. -/
@[category test, AMS 5 11]
theorem f_two : f 2 = 1 := by
  have h₁ : 1 ≤ f 2 :=
    le_f fun B _ => ⟨{3}, admissible_singleton (by decide) B, by simp⟩
  have h₂ : f 2 ≤ 1 := (f_le_card_I 2).trans_eq (by decide)
  exact le_antisymm h₂ h₁

/-- `I 3 = {4, 5}` and `f 3 = 2`. The admissible `C` depends on `B`: `C = {4}` if `9 ∈ B`
and `C = {4, 5}` otherwise. With the quantifiers in the order `∃ C, ∀ B`, or with
$\lvert B\rvert$ omitted from the score, the value would be `1`. -/
@[category test, AMS 5 11]
theorem f_three : f 3 = 2 := by
  have h₁ : 2 ≤ f 3 := le_f fun B _ => by
    by_cases h9 : 9 ∈ B
    · exact ⟨{4}, admissible_singleton (by decide) B, by simpa using Finset.card_pos.2 ⟨9, h9⟩⟩
    · exact ⟨{4, 5}, ⟨by decide, by simp [h9]⟩, by simp⟩
  have h₂ : f 3 ≤ 2 := (f_le_card_I 3).trans_eq (by decide)
  exact le_antisymm h₂ h₁

/--
Let $f(n)$ be maximal such that if $B\subset (2n,4n)\cap \mathbb{N}$ there exists some
$C\subset (n,2n)\cap \mathbb{N}$ such that $c_1+c_2\not\in B$ for all $c_1\neq c_2\in C$ and
$\lvert C\rvert+\lvert B\rvert \geq f(n)$.

Estimate $f(n)$. In particular is it true that $f(n)\leq n^{1/2+o(1)}$?

This formalizes only the upper-bound question: for every $\varepsilon > 0$,
$f(n) \leq n^{1/2+\varepsilon}$ for all sufficiently large $n$.
The lower bound and the broader estimation question are not formalized here.
-/
@[category research open, question, AMS 5 11]
theorem erdos_788.upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
  sorry

end Erdos788

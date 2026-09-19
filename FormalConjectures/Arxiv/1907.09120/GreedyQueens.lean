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
# Greedy queens on the single-quadrant board

Walk along the successive antidiagonals of an $\mathbb{N} \times \mathbb{N}$ chessboard, each in
order of increasing column, and place a queen on each square that is not attacked by an earlier
queen. Every column receives exactly one queen. Let $S_c$ be the row of the queen in column $c$.
The first $50000$ queens lie almost exactly on two lines of slopes $\varphi$ and $1/\varphi$,
where $\varphi$ is the golden ratio.

*References:*
- [arxiv/1907.09120](https://arxiv.org/abs/1907.09120)
  **Queens in exile: non-attacking queens on infinite chess boards**
  by *F. Michel Dekking, Jeffrey Shallit, N. J. A. Sloane*,
  Electron. J. Combin. 27(1) (2020), #P1.52. See Section 8, where this is Conjecture 25.
- [A275895](https://oeis.org/A275895) and [A065188](https://oeis.org/A065188)
- [First Alfa](https://www.nqueens.de/sub/FirstAlfa.en.html) on nqueens.de
-/

@[expose] public section

namespace Arxiv.«1907.09120»

open scoped goldenRatio

/--
`IsSafe f c r` says that a queen in row `r` of column `c` shares no row and no diagonal with the
queen in row `f c'` of column `c'`, for each `c' < c`.
-/
def IsSafe (f : ℕ → ℕ) (c r : ℕ) : Prop :=
  ∀ c' < c, f c' ≠ r ∧ f c' + c ≠ r + c' ∧ f c' + c' ≠ r + c

instance (f : ℕ → ℕ) (c : ℕ) : DecidablePred (IsSafe f c) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ _ < _, _))

@[category API, AMS 5]
theorem exists_isSafe (f : ℕ → ℕ) (c : ℕ) : ∃ r, IsSafe f c r := by
  refine ⟨∑ i ∈ Finset.range c, f i + c + 1, fun c' hc' ↦ ?_⟩
  have := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (f i)) (Finset.mem_range.2 hc')
  omega

/--
`queenRows n` lists the rows of the queens in columns `0, …, n - 1`. Each queen goes in the lowest
row that no queen in an earlier column attacks.
-/
def queenRows : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := queenRows n
    l ++ [Nat.find (exists_isSafe (l.getD · 0) n)]

/--
`greedyQueens c` is the row $S_c$ of the queen in column $c$.

This is the column-by-column version of the problem, due to Knuth. Dekking, Shallit and Sloane
note that it gives the same queens as the scan along antidiagonals.
-/
def greedyQueens (c : ℕ) : ℕ :=
  (queenRows (c + 1)).getD c 0

@[category API, AMS 5]
theorem length_queenRows (n : ℕ) : (queenRows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [queenRows, ih]

@[category API, AMS 5]
theorem getD_queenRows {c n : ℕ} (h : c < n) : (queenRows n).getD c 0 = greedyQueens c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · simp only [queenRows]
      rw [List.getD_append _ _ _ _ (by simpa [length_queenRows] using h), ih h]
    · rfl

/-- `greedyQueens c` is the lowest row that no queen in an earlier column attacks. -/
@[category API, AMS 5]
theorem greedyQueens_eq_find (c : ℕ) :
    greedyQueens c = Nat.find (exists_isSafe greedyQueens c) := by
  have key : ∀ r, IsSafe ((queenRows c).getD · 0) c r ↔ IsSafe greedyQueens c r :=
    fun r ↦ forall₂_congr fun c' hc' ↦ by simp only [getD_queenRows hc']
  rw [greedyQueens, queenRows]
  simp only [List.getD_append_right _ _ _ _ (length_queenRows c).le, length_queenRows,
    Nat.sub_self, List.getD_cons_zero]
  exact Nat.find_congr' (key _)

/-- The first terms of $S_c$, as listed in the paper and in A275895. -/
@[category test, AMS 5]
theorem greedyQueens_first_terms :
    (List.range 22).map greedyQueens =
      [0, 2, 4, 1, 3, 8, 10, 12, 14, 5, 7, 18, 6, 21, 9, 24, 26, 28, 30, 11, 13, 34] := by
  native_decide

/--
**Conjecture 25.** There are constants $\epsilon_1, \epsilon_2$ such that
$|S_c - c\varphi| < \epsilon_1$ if $S_c > c$, and $|S_c - c/\varphi| < \epsilon_2$ if $S_c < c$.
-/
@[category research open, AMS 5]
theorem conjecture25 :
    ∃ ε₁ ε₂ : ℝ, ∀ c : ℕ,
      (c < greedyQueens c → |(greedyQueens c : ℝ) - c * φ| < ε₁) ∧
      (greedyQueens c < c → |(greedyQueens c : ℝ) - c / φ| < ε₂) := by
  sorry

end Arxiv.«1907.09120»

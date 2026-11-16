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
# Density of ones in the Kolakoski sequence

The Kolakoski sequence is the self-describing sequence of ones and twos whose terms are the
lengths of its successive runs. Its official indexing begins with $a(1) = 1$; here it is extended
by $a(0) = 0$.

*References:*
- [A000002](https://oeis.org/A000002)
- E. S. Kupin and E. S. Rowland,
  ["Bounds on the frequency of 1 in the Kolakoski word"](https://arxiv.org/abs/0809.2776),
  arXiv:0809.2776 [math.CO] (2008).
-/

@[expose] public section

namespace OeisA2

/--
`wordPrefix n` is the finite Kolakoski word after expanding `n` runs beyond the seed `[1, 2, 2]`.
At stage $n$, position $n+2$ supplies the next run length, and the emitted symbol is $1$ for
even $n$ and $2$ for odd $n$.
-/
def wordPrefix : ℕ → List ℕ
  | 0 => [1, 2, 2]
  | n + 1 =>
      let xs := wordPrefix n
      let runLength := if xs.getD (n + 2) 1 = 2 then 2 else 1
      let nextSymbol := if n % 2 = 0 then 1 else 2
      xs ++ List.replicate runLength nextSymbol

/-- Every generated prefix is long enough for the next unread run length. -/
@[category API, AMS 11 68]
theorem prefix_length (n : ℕ) : n + 3 ≤ (wordPrefix n).length := by
  induction n with
  | zero => norm_num [wordPrefix]
  | succ n ih =>
      simp only [wordPrefix, List.length_append, List.length_replicate]
      split <;> omega

/-- The read cursor used to generate the next run is always inside the generated prefix. -/
@[category API, AMS 11 68]
theorem cursor_lt_prefix_length (n : ℕ) : n + 2 < (wordPrefix n).length := by
  have h := prefix_length n
  omega

/-- Every symbol in every generated prefix is either `1` or `2`. -/
@[category API, AMS 11 68]
theorem prefix_mem_one_or_two (n : ℕ) : ∀ x ∈ wordPrefix n, x = 1 ∨ x = 2 := by
  induction n with
  | zero => simp [wordPrefix]
  | succ n ih =>
      intro x hx
      simp only [wordPrefix, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ih x hx
      · rw [List.eq_of_mem_replicate hx]
        by_cases h : n % 2 = 0 <;> simp [h]

/-- The Kolakoski sequence, using its official one-based indexing and extended by `a 0 = 0`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (wordPrefix n).getD n 0

/-- Every positive-index term of the public sequence is one or two. -/
@[category API, AMS 11 68]
theorem a_one_or_two {n : ℕ} (hn : 0 < n) : a n = 1 ∨ a n = 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hlt : n < (wordPrefix n).length := by
    have h := prefix_length n
    omega
  apply prefix_mem_one_or_two n
  rw [a]
  have hget : (wordPrefix n).getD n 0 = (wordPrefix n)[n] :=
    List.getD_eq_getElem (l := wordPrefix n) (d := 0) hlt
  rw [hget]
  exact List.getElem_mem hlt

@[category test, AMS 11 68]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11 68]
theorem a_1 : a 1 = 1 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_2 : a 2 = 2 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_3 : a 3 = 2 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_4 : a 4 = 1 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_5 : a 5 = 1 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_6 : a 6 = 2 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_7 : a 7 = 1 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_8 : a 8 = 2 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_9 : a 9 = 2 := by norm_num [a, wordPrefix]

@[category test, AMS 11 68]
theorem a_10 : a 10 = 1 := by norm_num [a, wordPrefix]

/--
"It is an unsolved problem to show that the density of 1's is equal to 1/2."
— [A000002](https://oeis.org/A000002)
-/
@[category research open, AMS 11 68]
theorem density_one : {n : ℕ | a n = 1}.HasDensity (1 / 2 : ℝ) := by
  sorry

end OeisA2

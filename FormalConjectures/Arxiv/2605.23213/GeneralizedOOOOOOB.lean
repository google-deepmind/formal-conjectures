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
# Generalizing OOOOOOB: Versions B and C

*References:*
- [arxiv/2605.23213](https://arxiv.org/abs/2605.23213)
  **Generalizing OOOOOOB** by *Paul Ellis et al.* (2026)

The classic two-pile game *one-or-one-or-one-of-both* (OOOOOOB) lets a player take a token from
one pile, from the other pile, or one token from each pile. The player who makes the last move
wins. The paper studies three multi-pile generalizations, among them:

* **Version B**: a player removes a single token from any pile, or one token from every
  (nonempty) pile.
* **Version C**: a player removes a single token from any pile, or chooses two different piles
  and removes one token from each.

A position is described, as in the paper, by its *count vector* `[a₁, …, aₙ]`, where `aᵢ` is the
number of piles of size `i`.

The paper states two conjectures that predict P-positions from parities. Both are false.

* **Version B.** With `k ≥ 3` piles, each of size more than `⌈k / 3⌉`, the P/N status is
  conjectured to depend only on `k` and on the number of odd piles. For `k = 12` (so every pile
  has at least `5` tokens) this fails: the piles `5,5,5,5,5,5,5,6,6,6,6,6` (`7` odd piles,
  `65` tokens) form an N-position (removing one token from every pile wins), while the
  conjecture predicts a P-position. Moreover `5,5,5,5,5,5,6,6,6,6,6,6` (`6` odd piles) is a
  P-position, against the prediction. The authors verified up to `11` piles; `12` is the first
  failure.
* **Version C.** If every pile size `1, …, n` occurs at least twice (and the position is not
  `1,1,2,2,3,3,3`), the position is conjectured to be a P-position exactly when the number of
  tokens is a multiple of `3`. The position `[2, 2, 2, 2, 2, 2, 3]`, i.e. the piles
  `1,1,2,2,3,3,4,4,5,5,6,6,7,7,7` with `63` tokens, is an N-position: taking one token from each
  of the two piles of size `1` leads to the P-position `[0, 2, 2, 2, 2, 2, 3]`. This is the
  counterexample with the fewest tokens. Conversely, `[2, 2, 2, 2, 2, 2, 4]` (`70` tokens) is a
  P-position. The authors verified `aᵢ ≤ 5` and `n ≤ 5`.

  The Version C conjecture is stated in the paper for every `n`, but for `n = 2` it already
  fails by the paper's own Lemma on piles of size at most `3`, which lists the N-positions
  `(a₁, a₂) = (2, 3k + 2)`. We therefore state it with `n ≥ 3`.

The P/N status of a position is certified by a table of all positions reachable from it, in
which every position comes after all of its options. The table is computed and checked with
`native_decide`, and `sound_foldlM` shows that any table passing the check is correct.
-/

@[expose] public section

namespace Arxiv.«2605.23213»

open Std

/-- A position: `a = [a₁, …, aₙ]`, where `aᵢ` is the number of piles of size `i`. -/
abbrev Position := List ℕ

/-- The total number of tokens `∑ i * aᵢ` of a position. -/
def tokens (a : Position) : ℕ :=
  ((List.range a.length).zip a).foldr (fun p s => (p.1 + 1) * p.2 + s) 0

/-- The number of piles of odd size, `a₁ + a₃ + a₅ + ⋯`. -/
def oddPiles (a : Position) : ℕ :=
  ((List.range a.length).zip a).foldr (fun p s => if p.1 % 2 = 0 then p.2 + s else s) 0

/-- Remove one token from one of the piles of size `i + 1`: it becomes a pile of size `i`
(and disappears when `i = 0`). -/
def takeOne (a : Position) (i : ℕ) : Position :=
  if i = 0 then a.modify 0 (· - 1) else (a.modify i (· - 1)).modify (i - 1) (· + 1)

/-- The positions reached by removing a single token from some pile. -/
def singleOptions (a : Position) : List Position :=
  ((List.range a.length).filter (fun i => 1 ≤ a.getD i 0)).map (takeOne a)

/-- The options of a position in Version B: remove one token from a pile, or one token from
every pile (piles of size `i + 1` become piles of size `i`, so the counts shift down by one).
The second move needs at least one pile. -/
def optionsB (a : Position) : List Position :=
  singleOptions a ++ if a.any (· ≠ 0) then [a.tail ++ [0]] else []

/-- The options of a position in Version C: remove one token from a pile of size `i + 1`, or
remove one token from each of two different piles, of sizes `i + 1` and `j + 1` with `i ≤ j`
(two piles of the same size `i + 1` need `aᵢ₊₁ ≥ 2`). -/
def optionsC (a : Position) : List Position :=
  singleOptions a ++
  (List.range a.length).flatMap fun i =>
    ((List.range a.length).filter fun j =>
      i < j ∧ 1 ≤ a.getD i 0 ∧ 1 ≤ a.getD j 0 ∨ i = j ∧ 2 ≤ a.getD i 0).map
        fun j => takeOne (takeOne a i) j

mutual
/-- `IsP opts a`: in the game whose moves are given by `opts`, the position `a` is a
P-position (the previous player wins), i.e. every option of `a` is an N-position. -/
inductive IsP (opts : Position → List Position) : Position → Prop
  | mk (a : Position) : (∀ b ∈ opts a, IsN opts b) → IsP opts a
/-- `IsN opts a`: the position `a` is an N-position (the next player wins), i.e. some option of
`a` is a P-position. -/
inductive IsN (opts : Position → List Position) : Position → Prop
  | mk (a b : Position) : b ∈ opts a → IsP opts b → IsN opts a
end

variable {opts : Position → List Position}

/-- No position is both an N-position and a P-position. -/
@[category API, AMS 5 91]
theorem IsN.not_isP {a : Position} (h : IsN opts a) : ¬ IsP opts a :=
  IsN.rec (motive_1 := fun a _ => ¬ IsN opts a) (motive_2 := fun a _ => ¬ IsP opts a)
    (fun _ _ ih hN => by
      cases hN with
      | mk _ b hb hPb => exact ih b hb hPb)
    (fun _ b hb _ ih hP => by
      cases hP with
      | mk _ hall => exact ih (hall b hb))
    h

/-- No position is both a P-position and an N-position. -/
@[category API, AMS 5 91]
theorem IsP.not_isN {a : Position} (h : IsP opts a) : ¬ IsN opts a := fun hN => hN.not_isP h

/-- One step of the certificate checker: `x` may be added once all its options are in the table,
with value `true` (P-position) exactly when none of its options has value `true`. -/
def checkStep (opts : Position → List Position) (M : HashMap Position Bool) (x : Position) :
    Option (HashMap Position Bool) :=
  if (opts x).all (fun y => M.contains y) then
    some (M.insert x !((opts x).any fun y => M.getD y false))
  else none

/-- A table is *sound* if its `true` entries are P-positions and its `false` entries are
N-positions. -/
def Sound (opts : Position → List Position) (M : HashMap Position Bool) : Prop :=
  ∀ x b, M[x]? = some b → (b = true → IsP opts x) ∧ (b = false → IsN opts x)

@[category API, AMS 5 91]
theorem sound_checkStep {M M' : HashMap Position Bool} {x : Position} (hM : Sound opts M)
    (h : checkStep opts M x = some M') : Sound opts M' := by
  unfold checkStep at h
  split_ifs at h with hall
  cases h
  intro y b hy
  rw [HashMap.getElem?_insert] at hy
  split_ifs at hy with hxy
  · cases hy
    have hxy' : x = y := by simpa using hxy
    subst hxy'
    rw [List.all_eq_true] at hall
    constructor
    · intro hb
      refine IsP.mk x fun z hz => ?_
      have hz' : M.getD z false = false := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hb
        simpa using hb z hz
      have hc := hall z hz
      rw [HashMap.getD_eq_getD_getElem?] at hz'
      rw [HashMap.contains_eq_isSome_getElem?] at hc
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hc
      rw [hc'] at hz'
      simp only [Option.getD_some] at hz'
      subst hz'
      exact (hM z false hc').2 rfl
    · intro hb
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false, List.any_eq_true] at hb
      obtain ⟨z, hz, hz'⟩ := hb
      rw [HashMap.getD_eq_getD_getElem?] at hz'
      cases hc : M[z]? with
      | none => rw [hc] at hz'; simp at hz'
      | some c =>
        rw [hc] at hz'
        simp only [Option.getD_some] at hz'
        subst hz'
        exact IsN.mk x z hz ((hM z true hc).1 rfl)
  · exact hM y b hy

/-- Any table built by `checkStep` from a sound table is sound. -/
@[category API, AMS 5 91]
theorem sound_foldlM (order : List Position) :
    ∀ {M M' : HashMap Position Bool}, Sound opts M → order.foldlM (checkStep opts) M = some M' →
      Sound opts M' := by
  induction order with
  | nil =>
    intro M M' hM h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact hM
  | cons x xs ih =>
    intro M M' hM h
    simp only [List.foldlM_cons] at h
    cases hs : checkStep opts M x with
    | none => rw [hs] at h; simp at h
    | some M₁ =>
      rw [hs] at h
      exact ih (sound_checkStep hM hs) h

@[category API, AMS 5 91]
theorem sound_empty : Sound opts ({} : HashMap Position Bool) := by
  intro x b h
  simp at h

/-- All positions reachable from `start`, each listed after all of its options (an iterative
depth-first search; `fuel` bounds the number of steps). Its correctness is not needed: the
output is checked by `checkStep`. -/
def reachOrder (opts : Position → List Position) (start : Position) (fuel : ℕ) :
    Array Position := Id.run do
  let mut visited : HashSet Position := {}
  let mut out : Array Position := #[]
  let mut stack : List (Position × Bool) := [(start, false)]
  for _ in [0:fuel] do
    match stack with
    | [] => break
    | (x, true) :: rest =>
      stack := rest
      out := out.push x
    | (x, false) :: rest =>
      if visited.contains x then
        stack := rest
      else
        visited := visited.insert x
        stack := (opts x).map (·, false) ++ (x, true) :: rest
  return out

/-- The value of `start` in the checked table of the positions reachable from it. -/
def evalCert (opts : Position → List Position) (start : Position) : Option Bool :=
  ((reachOrder opts start 10000000).toList.foldlM (checkStep opts) {}).bind fun M => M[start]?

@[category API, AMS 5 91]
theorem isN_of_evalCert {a : Position} (h : evalCert opts a = some false) : IsN opts a := by
  unfold evalCert at h
  cases hM : (reachOrder opts a 10000000).toList.foldlM (checkStep opts) {} with
  | none => rw [hM] at h; simp at h
  | some M =>
    rw [hM] at h
    exact ((sound_foldlM _ sound_empty hM) a false h).2 rfl

@[category API, AMS 5 91]
theorem isP_of_evalCert {a : Position} (h : evalCert opts a = some true) : IsP opts a := by
  unfold evalCert at h
  cases hM : (reachOrder opts a 10000000).toList.foldlM (checkStep opts) {} with
  | none => rw [hM] at h; simp at h
  | some M =>
    rw [hM] at h
    exact ((sound_foldlM _ sound_empty hM) a true h).1 rfl

/-! ## Tests -/

/-- The piles `1, 2, 3` (one of each size) have `6` tokens, two of them odd. -/
@[category test, AMS 5 91]
theorem tokens_one_one_one : tokens [1, 1, 1] = 6 ∧ oddPiles [1, 1, 1] = 2 := by decide +kernel

/-- In Version C, from the piles `1, 1` one can take one token or both tokens. -/
@[category test, AMS 5 91]
theorem optionsC_two : optionsC [2] = [[1], [0]] := by decide +kernel

/-- In Version B, from the piles `1, 2` one can take a token from either pile, or one token from
both piles, leaving the single pile `1`. -/
@[category test, AMS 5 91]
theorem optionsB_one_one : optionsB [1, 1] = [[0, 1], [2, 0], [1, 0]] := by decide +kernel

/-- In Version B, `(a₁, a₂, a₃) = (1, 1, 1)` is a P-position, by the paper's Lemma on piles of
size at most `3`. -/
@[category test, AMS 5 91]
theorem isP_B_one_one_one : IsP optionsB [1, 1, 1] := isP_of_evalCert (by native_decide)

/-- In Version C, the paper's exceptional position `1,1,2,2,3,3,3` is an N-position although it
has `15` tokens. -/
@[category test, AMS 5 91]
theorem isN_C_two_two_three : IsN optionsC [2, 2, 3] := isN_of_evalCert (by native_decide)

/-- In Version C, `(a₁, a₂, a₃) = (1, 0, 2)` is a P-position, by the paper's Lemma on piles of
size at most `3`. -/
@[category test, AMS 5 91]
theorem isP_C_one_zero_two : IsP optionsC [1, 0, 2] := isP_of_evalCert (by native_decide)

/-! ## Version B -/

/-- The prediction of the Version B conjecture for `k` piles of which `o` are odd:
* if `k` is odd, `o` is even;
* if `k ≡ 0 (mod 4)`, `o ∈ {0, 2, …, k/2 - 2} ∪ {k/2 + 1, …, k - 3, k - 1}`;
* if `k ≡ 2 (mod 4)`, `o ∈ {0, 2, …, k/2 - 1} ∪ {k/2 + 2, …, k - 3, k - 1}`. -/
def predictedB (k o : ℕ) : Prop :=
  if k % 2 = 1 then Even o
  else if k % 4 = 0 then (Even o ∧ o + 2 ≤ k / 2) ∨ (Odd o ∧ k / 2 + 1 ≤ o)
  else (Even o ∧ o + 1 ≤ k / 2) ∨ (Odd o ∧ k / 2 + 2 ≤ o)

/-- The certificate computation for the piles `5,5,5,5,5,5,5,6,6,6,6,6`. -/
@[category API, AMS 5 91]
theorem evalCert_B_seven_five : evalCert optionsB [0, 0, 0, 0, 7, 5] = some false := by
  native_decide

/-- The certificate computation for the piles `5,5,5,5,5,5,6,6,6,6,6,6`. -/
@[category API, AMS 5 91]
theorem evalCert_B_six_six : evalCert optionsB [0, 0, 0, 0, 6, 6] = some true := by
  native_decide

/--
**Conjecture (Ellis et al., 2026), Version B.** Suppose there are `k ≥ 3` piles, each with more
than `m = ⌈k / 3⌉` tokens. Then the position is a P-position exactly when its number of odd piles
is as described by `predictedB`.

Here `k = a₁ + ⋯ + aₙ` and `⌈k / 3⌉ = (k + 2) / 3`, so the hypothesis says that `aᵢ = 0` for
`i ≤ (k + 2) / 3`. The conjecture is false: the twelve piles `5,5,5,5,5,5,5,6,6,6,6,6` have
`7` odd piles, so the conjecture predicts a P-position, but removing one token from every pile
wins.
-/
@[category research solved, AMS 5 91]
theorem version_b_conjecture :
    ¬ ∀ a : Position, 3 ≤ a.sum → (∀ i, i + 1 ≤ (a.sum + 2) / 3 → a.getD i 0 = 0) →
      (IsP optionsB a ↔ predictedB a.sum (oddPiles a)) := by
  intro h
  have hN : IsN optionsB [0, 0, 0, 0, 7, 5] := isN_of_evalCert evalCert_B_seven_five
  refine hN.not_isP ((h [0, 0, 0, 0, 7, 5] (by decide +kernel) ?_).2 ?_)
  · intro i hi
    have hi' : i < 4 := by simp at hi; omega
    interval_cases i <;> rfl
  · simp only [predictedB]
    decide +kernel

/-- The other direction fails as well: the twelve piles `5,5,5,5,5,5,6,6,6,6,6,6` have `6` odd
piles, so the conjecture predicts an N-position, but they form a P-position. -/
@[category research solved, AMS 5 91]
theorem version_b_conjecture.variants.p_position :
    IsP optionsB [0, 0, 0, 0, 6, 6] ∧ ¬ predictedB 12 (oddPiles [0, 0, 0, 0, 6, 6]) :=
  ⟨isP_of_evalCert evalCert_B_six_six, by simp only [predictedB]; decide +kernel⟩

/-! ## Version C -/

/-- The certificate computation for `[2, 2, 2, 2, 2, 2, 3]`. -/
@[category API, AMS 5 91]
theorem evalCert_C_two_three : evalCert optionsC [2, 2, 2, 2, 2, 2, 3] = some false := by
  native_decide

/-- The certificate computation for `[2, 2, 2, 2, 2, 2, 4]`. -/
@[category API, AMS 5 91]
theorem evalCert_C_two_four : evalCert optionsC [2, 2, 2, 2, 2, 2, 4] = some true := by
  native_decide

/-- Taking one token from each pile of size `1` is a winning move from `[2, 2, 2, 2, 2, 2, 3]`. -/
@[category test, AMS 5 91]
theorem winning_move_C : [0, 2, 2, 2, 2, 2, 3] ∈ optionsC [2, 2, 2, 2, 2, 2, 3] ∧
    IsP optionsC [0, 2, 2, 2, 2, 2, 3] :=
  ⟨by decide +kernel, isP_of_evalCert (by native_decide)⟩

/--
**Conjecture (Ellis et al., 2026), Version C.** Suppose a position of Version C has `aᵢ` piles
of size `i` for `1 ≤ i ≤ n`, with `aᵢ ≥ 2` for every `i`, and is not `1,1,2,2,3,3,3`. Then it is
a P-position if and only if its number of tokens is a multiple of `3`.

Here `n ≥ 3` (see the module docstring). The conjecture is false: `[2, 2, 2, 2, 2, 2, 3]` has
`63` tokens but is an N-position.
-/
@[category research solved, AMS 5 91]
theorem version_c_conjecture :
    ¬ ∀ a : Position, 3 ≤ a.length → (∀ x ∈ a, 2 ≤ x) → a ≠ [2, 2, 3] →
      (IsP optionsC a ↔ tokens a % 3 = 0) := by
  intro h
  have hN : IsN optionsC [2, 2, 2, 2, 2, 2, 3] := isN_of_evalCert evalCert_C_two_three
  exact hN.not_isP ((h [2, 2, 2, 2, 2, 2, 3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel))

/-- The other direction fails as well: `[2, 2, 2, 2, 2, 2, 4]` has `70` tokens but is a
P-position. -/
@[category research solved, AMS 5 91]
theorem version_c_conjecture.variants.p_position :
    IsP optionsC [2, 2, 2, 2, 2, 2, 4] ∧ tokens [2, 2, 2, 2, 2, 2, 4] % 3 = 1 :=
  ⟨isP_of_evalCert evalCert_C_two_four, by decide +kernel⟩

/-- For `n = 2` the statement fails at `(a₁, a₂) = (2, 2)`: the piles `1, 1, 2, 2` have `6`
tokens but form an N-position, as the paper's own Lemma on small piles shows. -/
@[category research solved, AMS 5 91]
theorem version_c_conjecture.variants.two_sizes :
    IsN optionsC [2, 2] ∧ tokens [2, 2] % 3 = 0 :=
  ⟨isN_of_evalCert (by native_decide), by decide +kernel⟩

end Arxiv.«2605.23213»

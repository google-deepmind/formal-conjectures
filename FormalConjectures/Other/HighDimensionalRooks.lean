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
# Forced checkmate with rooks in higher dimensions

The board is $\mathbb Z^d$. A rook moves by changing one coordinate to any value, and the king
moves by changing any set of coordinates by $\pm 1$. Does some finite number of white rooks
suffice to force checkmate against a lone black king, provided the king starts sufficiently far
from every rook?

Known status:

- For $d = 3$, yes. George Lowther's construction (2012) uses $96$ rooks.
- For $d = 4$, the question is open.
- For $d \ge 5$, no. Tesseract and Matthew Bolan reduce this to Conway's angel problem. The case
  $d \ge 6$ was posted in 2025, and the case $d = 5$ was added in 2026.

White moves first, moving one rook per turn. Rooks cannot jump over other pieces. Black moves the
king and may capture undefended rooks. Neither side may pass. Stalemate and infinite play are not
White wins, and there is no move-count draw rule.

*References:*

- [Original question](https://math.stackexchange.com/q/155777)
- [Lowther's construction](https://math.stackexchange.com/a/156693)
- [Tesseract's impossibility argument](https://math.stackexchange.com/a/5093617)
- [Related MathOverflow discussion](https://mathoverflow.net/q/99124)
-/

@[expose] public section

namespace HighDimensionalRooks

/-- A square on the infinite board $\mathbb Z^d$. The inherited metric is Chebyshev distance. -/
abbrev Square (d : ℕ) := Fin d → ℤ

/-- A position with one black king and finitely many white rooks on distinct squares. -/
structure Position (d : ℕ) where
  king : Square d
  rooks : Finset (Square d)
  king_not_mem : king ∉ rooks

variable {d : ℕ}

/-- A rook can travel from `a` to `b` along one coordinate without crossing an occupied square.
Occupancy of the endpoints is handled separately by the move and attack definitions. -/
def RookReaches (occupied : Finset (Square d)) (a b : Square d) : Prop :=
  a ≠ b ∧ ∃ i, (∀ j, j ≠ i → a j = b j) ∧
    ∀ c ∈ occupied, (∀ j, j ≠ i → c j = a j) →
      c i ∉ Set.Ioo (min (a i) (b i)) (max (a i) (b i))

/-- The king is attacked by a rook along an unobstructed coordinate line. -/
def Position.InCheck (p : Position d) : Prop :=
  ∃ r ∈ p.rooks, RookReaches p.rooks r p.king

/-- Move the king to `k`, removing any rook it captures. Legality is checked separately. -/
def Position.moveKing (p : Position d) (k : Square d) : Position d where
  king := k
  rooks := p.rooks.erase k
  king_not_mem := Finset.notMem_erase _ _

/-- A legal king move changes each coordinate by at most one, changes at least one coordinate,
and leaves the king out of check after any capture. -/
def Position.KingCanMoveTo (p : Position d) (k : Square d) : Prop :=
  p.king ≠ k ∧ (∀ i, |k i - p.king i| ≤ 1) ∧ ¬(p.moveKing k).InCheck

/-- A legal White move moves exactly one rook to an empty square. Rooks cannot cross pieces
or capture the king. A White turn begins with the black king out of check. -/
def Position.WhiteMove (p q : Position d) : Prop :=
  ¬p.InCheck ∧ q.king = p.king ∧
    ∃ r ∈ p.rooks, ∃ s, s ∉ insert p.king p.rooks ∧
      RookReaches (insert p.king p.rooks) r s ∧ q.rooks = insert s (p.rooks.erase r)

/-- Checkmate means that the king is in check and has no legal move. -/
def Position.IsCheckmate (p : Position d) : Prop :=
  p.InCheck ∧ ¬∃ k, p.KingCanMoveTo k

/-- The side whose turn it is. -/
inductive Turn
  | white
  | black

/-- White can force checkmate in finite play. White chooses a legal successor; every legal
Black reply must remain winning. The Black move constructor requires a legal reply to exist,
so stalemate is not a win. The inductive definition excludes infinite play. -/
inductive CanForceMate : Turn → Position d → Prop
  | checkmate {p} : p.IsCheckmate → CanForceMate .black p
  | white {p q} : p.WhiteMove q → CanForceMate .black q → CanForceMate .white p
  | black {p} : (∃ k, p.KingCanMoveTo k) →
      (∀ k, p.KingCanMoveTo k → CanForceMate .white (p.moveKing k)) →
      CanForceMate .black p

/-- The king cannot pass. -/
@[category test, AMS 5 91]
theorem king_cannot_stay (p : Position d) : ¬p.KingCanMoveTo p.king := by
  simp [Position.KingCanMoveTo]

/-- A rook cannot jump over another piece. -/
@[category test, AMS 5 91]
theorem rook_cannot_jump :
    ¬RookReaches {![1, 0, 0, 0]} ![0, 0, 0, 0] ![2, 0, 0, 0] := by
  unfold RookReaches
  decide

/-- The king can capture an adjacent undefended rook. -/
@[category test, AMS 5 91]
theorem king_can_capture_undefended_rook :
    (Position.mk ![0, 0, 0, 0] {![1, 0, 0, 0]} (by decide)).KingCanMoveTo
      ![1, 0, 0, 0] := by
  unfold Position.KingCanMoveTo Position.moveKing Position.InCheck RookReaches
  decide

/-- Capturing a rook is illegal if a second rook would then attack the king. -/
@[category test, AMS 5 91]
theorem king_cannot_capture_defended_rook :
    ¬(Position.mk ![0, 0, 0, 0] {![1, 0, 0, 0], ![2, 0, 0, 0]} (by decide)).KingCanMoveTo
      ![1, 0, 0, 0] := by
  unfold Position.KingCanMoveTo Position.moveKing Position.InCheck RookReaches
  decide

/-- White cannot force mate without any rooks. -/
@[category test, AMS 5 91]
theorem not_canForceMate_white_empty (p : Position d) (h : p.rooks = ∅) :
    ¬CanForceMate .white p := by
  intro hw
  cases hw with
  | white hm _ =>
    obtain ⟨_, _, r, hr, _⟩ := hm
    simp [h] at hr

/-- A stalemated king does not give White a win. -/
@[category test, AMS 5 91]
theorem not_canForceMate_of_stalemate (p : Position d) (hc : ¬p.InCheck)
    (hm : ¬∃ k, p.KingCanMoveTo k) : ¬CanForceMate .black p := by
  intro hw
  cases hw with
  | checkmate h => exact hc h.1
  | black h _ => exact hm h

/-- Two rooks on opposite sides of the king give checkmate on a one-dimensional board. -/
@[category test, AMS 5 91]
theorem checkmate_in_one_dimension : (Position.mk ![0] {![-1], ![1]} (by decide)).IsCheckmate := by
  constructor
  · unfold Position.InCheck RookReaches
    decide
  · rintro ⟨k, hne, hstep, hsafe⟩
    have hbound := hstep 0
    simp only [Matrix.cons_val_zero] at hbound
    rw [abs_le] at hbound
    have hk : k = ![-1] ∨ k = ![0] ∨ k = ![1] := by
      have : k 0 = -1 ∨ k 0 = 0 ∨ k 0 = 1 := by omega
      rcases this with h | h | h <;>
        simp_all [funext_iff, Fin.forall_fin_one]
    rcases hk with rfl | rfl | rfl
    · exact hsafe (by unfold Position.moveKing Position.InCheck RookReaches; decide)
    · exact hne rfl
    · exact hsafe (by unfold Position.moveKing Position.InCheck RookReaches; decide)

/--
`RooksCanForceMate d` says that there are integers $R, D \ge 1$ such that White can force
checkmate on $\mathbb Z^d$ from every position with $R$ rooks, White to move, the king out of
check, and every rook at Chebyshev distance at least $D$ from the king.

The distance condition rules out immediate captures at the start. The rook count and the distance
are uniform over positions. The strategy and the time to mate may depend on the position.
-/
def RooksCanForceMate (d : ℕ) : Prop :=
  ∃ R D : ℕ, 0 < R ∧ 0 < D ∧ ∀ p : Position d,
    p.rooks.card = R → ¬p.InCheck →
      (∀ r ∈ p.rooks, (D : ℝ) ≤ dist p.king r) → CanForceMate .white p

/-- For $d \ge 2$, every rook count and distance are realised by a position that satisfies the
hypotheses of `RooksCanForceMate d`. So the statements below are not vacuous. For $d = 1$, the
nearest rook always checks the king. -/
@[category test, AMS 5 91]
theorem exists_initial_position (hd : 2 ≤ d) (R D : ℕ) :
    ∃ p : Position d, p.rooks.card = R ∧ ¬p.InCheck ∧
      ∀ r ∈ p.rooks, (D : ℝ) ≤ dist p.king r := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  let f : ℕ → Square d := fun j _ => (D + j + 1 : ℕ)
  have hf : Function.Injective f := by
    intro i j h
    have := congrFun h ⟨0, by omega⟩
    dsimp [f] at this
    omega
  have hzero : (0 : Square d) ∉ (Finset.range R).image f := by
    rintro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have := congrFun hj ⟨0, by omega⟩
    dsimp [f] at this
    omega
  let p : Position d := ⟨0, (Finset.range R).image f, hzero⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · simp [p, Finset.card_image_of_injective _ hf]
  · rintro ⟨r, hr, _, i, hi, _⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨k, hk⟩ := exists_ne i
    have := hi k hk
    dsimp [f, p] at this
    omega
  · intro r hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    change (D : ℝ) ≤ dist (fun _ : Fin d => (0 : ℤ)) (fun _ => (D + j + 1 : ℕ))
    simp only [dist_pi_const, Int.dist_eq, Int.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]

/--
Can some finite number of rooks force checkmate on $\mathbb Z^4$ when the king starts far from
every rook?
-/
@[category research open, AMS 5 91]
theorem four_dimensions : answer(sorry) ↔ RooksCanForceMate 4 := by
  sorry

/--
On $\mathbb Z^3$, a finite number of rooks can force checkmate when the king starts far from every
rook. [Lowther's construction](https://math.stackexchange.com/a/156693) (2012) uses $96$ rooks.
-/
@[category research solved, AMS 5 91]
theorem four_dimensions.variants.three : RooksCanForceMate 3 := by
  sorry

/--
On $\mathbb Z^d$ with $d \ge 5$, no finite number of rooks can force checkmate when the king starts
far from every rook.

This is the [answer by Tesseract and Matthew Bolan](https://math.stackexchange.com/a/5093617), in
which the king plays two copies of Conway's angel game at once. The answer is not peer reviewed.
For $5 \le d \le 7$, it relies on results about the angel game from an archived web page by
Oddvar Kloster. A comment by Bolan derives $d \ge 8$ from published proofs that the angel of
power $2$ wins in the plane.
-/
@[category research solved, AMS 5 91]
theorem four_dimensions.variants.at_least_five (hd : 5 ≤ d) : ¬RooksCanForceMate d := by
  sorry

end HighDimensionalRooks

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
# Derandomization of logarithmic space

$\mathsf{RL}$ is the class of languages decided in logarithmic space and polynomial time by a
randomized machine with one-sided error, and $\mathsf{BPL}$ the class with two-sided error. It
was believed that both equal $\mathsf{L}$, that is, that randomness does not help logarithmic
space computation. Earlier unconditional results include $\mathsf{RL} \subseteq \mathsf{SC}$
[Ni94], $\mathsf{BPL} \subseteq \mathsf{DSPACE}(\log^{3/2} n)$ [SZ99] and $\mathsf{SL} = \mathsf{L}$
[Re08].

The machine model below has a finite control, read-only two-way input heads on the input
between end markers, two-way work tapes, and one fresh random bit at each step. The work space
of a run is the number of distinct work cells visited. $\mathsf{L}$ uses deterministic machines
that always halt with the right answer; $\mathsf{RL}$ and $\mathsf{BPL}$ use machines that halt
within a polynomial number of steps on every coin sequence.

*References:*
- [Wikipedia: RL](https://en.wikipedia.org/wiki/RL_(complexity))
- [Wikipedia: BPL](https://en.wikipedia.org/wiki/BPL_(complexity))
- [Ni94] N. Nisan, *$\mathsf{RL} \subseteq \mathsf{SC}$*, Comput. Complexity 4 (1994), 1–11.
- [SZ99] M. Saks and S. Zhou, *$\mathrm{BP_HSPACE}(S) \subseteq \mathrm{DSPACE}(S^{3/2})$*,
  J. Comput. System Sci. 58 (1999), 376–403.
- [Re08] O. Reingold, *Undirected connectivity in log-space*, J. ACM 55 (2008), 1–24.
- [OAI26] OpenAI, *Exact Derandomization of Logarithmic Space: L equals RL equals BPL*. OpenAI
  Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/paper.pdf
-/

@[expose] public section

namespace LogspaceDerandomization

/-- Binary words. -/
abbrev Word := List Bool

/-- Languages over `{0, 1}`. -/
abbrev Language := Set Word

/-- An infinite sequence of random bits. -/
abbrev CoinTape := ℕ → Bool

/-- A head move. -/
inductive Direction where
  | left | stay | right
  deriving DecidableEq

/-- A symbol read on the input tape: an end marker or an input bit. -/
inductive InputSymbol where
  | leftMarker | bit (b : Bool) | rightMarker
  deriving DecidableEq

/-- Move a work head. -/
def Direction.move (d : Direction) (z : ℤ) : ℤ :=
  match d with
  | .left => z - 1
  | .stay => z
  | .right => z + 1

/-- Move an input head, staying between the end markers. -/
def Direction.moveInput (d : Direction) {n : ℕ} (i : Fin (n + 2)) : Fin (n + 2) :=
  match d with
  | .left => ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  | .stay => i
  | .right => ⟨min (i.val + 1) (n + 1), by omega⟩

/-- The symbol at position `i` of the input `x` framed by end markers. -/
def readInput (x : Word) (i : Fin (x.length + 2)) : InputSymbol :=
  if i.val = 0 then .leftMarker else
    match x[i.val - 1]? with
    | some b => .bit b
    | none => .rightMarker

/-- One transition: a new state, bits to write, and moves of the work and input heads. -/
structure Action (q w h : ℕ) where
  /-- The next state. -/
  nextState : Fin (q + 1)
  /-- The bit written on each work tape. -/
  write : Fin w → Bool
  /-- The move of each work head. -/
  workMove : Fin w → Direction
  /-- The move of each input head. -/
  inputMove : Fin h → Direction

/-- A machine with `q + 1` states, `w` work tapes and `h` input heads. A state with an output
is halting. The transition also sees the current random bit. -/
structure Machine (q w h : ℕ) where
  /-- The initial state. -/
  initialState : Fin (q + 1)
  /-- The answer of a halting state. -/
  output : Fin (q + 1) → Option Bool
  /-- The transition function. -/
  transition : Fin (q + 1) → (Fin h → InputSymbol) → (Fin w → Bool) → Bool →
    Action q w h

/-- A configuration on an input of length `n`. -/
structure Configuration (q w h n : ℕ) where
  /-- The current state. -/
  state : Fin (q + 1)
  /-- The input head positions. -/
  inputPos : Fin h → Fin (n + 2)
  /-- The work head positions. -/
  workPos : Fin w → ℤ
  /-- The work tape contents. -/
  work : Fin w → ℤ → Bool

namespace Machine

variable {q w h : ℕ}

/-- The initial configuration. -/
def initial (M : Machine q w h) (n : ℕ) : Configuration q w h n where
  state := M.initialState
  inputPos := fun _ => ⟨0, by omega⟩
  workPos := fun _ => 0
  work := fun _ _ => false

/-- One step on input `x` with random bit `b`; halting configurations are fixed. -/
def step (M : Machine q w h) (x : Word) (b : Bool)
    (c : Configuration q w h x.length) : Configuration q w h x.length :=
  match M.output c.state with
  | some _ => c
  | none =>
    let a := M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b
    { state := a.nextState
      inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
      workPos := fun k => (a.workMove k).move (c.workPos k)
      work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

/-- The configuration after `t` steps with coin sequence `coins`. -/
def run (M : Machine q w h) (x : Word) (coins : CoinTape) :
    ℕ → Configuration q w h x.length
  | 0 => M.initial x.length
  | t + 1 => M.step x (coins t) (M.run x coins t)

/-- The number of distinct work cells visited during the first `t` steps. -/
def spaceThrough (M : Machine q w h) (x : Word) (coins : CoinTape) (t : ℕ) : ℕ :=
  ∑ k : Fin w, ((Finset.range (t + 1)).image
    (fun s => (M.run x coins s).workPos k)).card

/-- The machine uses `O(log n)` work cells on every input, coin sequence and time. -/
def LogSpace (M : Machine q w h) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ (x : Word) (coins : CoinTape) (t : ℕ),
    M.spaceThrough x coins t ≤ c * Nat.clog 2 (x.length + 2)

/-- The transition ignores the random bit. -/
def Deterministic (M : Machine q w h) : Prop :=
  ∀ s i v, M.transition s i v false = M.transition s i v true

/-- On input `x` the machine has halted by time `t` on every coin sequence. -/
def HaltsBy (M : Machine q w h) (x : Word) (t : ℕ) : Prop :=
  ∀ coins : CoinTape, ∃ b : Bool, M.output (M.run x coins t).state = some b

/-- The machine decides `A`: on every input it halts with the right answer on every coin
sequence. -/
def Decides (M : Machine q w h) (A : Language) : Prop :=
  ∀ x : Word, ∃ (t : ℕ) (b : Bool),
    (b = true ↔ x ∈ A) ∧ ∀ coins : CoinTape,
      M.output (M.run x coins t).state = some b

/-- Extend `t` random bits by zeros. -/
def extendCoins {t : ℕ} (bits : Fin t → Bool) : CoinTape :=
  fun s => if hs : s < t then bits ⟨s, hs⟩ else false

/-- The probability of accepting `x` within `t` steps, over `t` uniform random bits. -/
def acceptanceProbability (M : Machine q w h) (x : Word) (t : ℕ) : ℚ :=
  ((Finset.univ.filter (fun bits : Fin t → Bool =>
    M.output (M.run x (extendCoins bits) t).state = some true)).card : ℚ) /
    (2 : ℚ) ^ t

end Machine

/-- The time bound `c (n + 2) ^ k`. -/
def polynomialClock (c k n : ℕ) : ℕ := c * (n + 2) ^ k

/-- Deterministic logarithmic space. -/
def L : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.Deterministic ∧ M.LogSpace ∧ M.Decides A}

/-- Randomized logarithmic space and polynomial time with one-sided error. -/
def RL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (1 / 2 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) = 0)}

/-- Randomized logarithmic space and polynomial time with two-sided error. -/
def BPL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (2 / 3 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) ≤ (1 / 3 : ℚ))}

set_option linter.style.formal_proof_palomar false in
/--
**$\mathsf{RL} = \mathsf{L}$**: randomized logarithmic space with one-sided error is no more
powerful than deterministic logarithmic space.

This was proved by an internal OpenAI model in September 2026 [OAI26]; see
`rl_eq_l.variants.openai` and the linked Lean proof.
-/
@[category research solved, AMS 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/Logspace/Equality.lean#L104"]
theorem rl_eq_l : RL = L := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
**$\mathsf{BPL} = \mathsf{L}$**: randomized logarithmic space with two-sided error is no more
powerful than deterministic logarithmic space.

This was proved by an internal OpenAI model in September 2026 [OAI26]; see
`rl_eq_l.variants.openai` and the linked Lean proof.
-/
@[category research solved, AMS 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/Logspace/Equality.lean#L104"]
theorem bpl_eq_l : BPL = L := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The statement of the linked Lean proof [OAI26]: $\mathsf{L} = \mathsf{RL} = \mathsf{BPL}$. -/
@[category research solved, AMS 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/Logspace/Equality.lean#L104"]
theorem rl_eq_l.variants.openai : L = RL ∧ RL = BPL := by
  sorry

/-- The linked statement gives `RL = L`. -/
@[category test, AMS 68]
theorem rl_eq_l_of_openai (h : type_of% rl_eq_l.variants.openai) : type_of% rl_eq_l :=
  h.1.symm

/-- The linked statement gives `BPL = L`. -/
@[category test, AMS 68]
theorem bpl_eq_l_of_openai (h : type_of% rl_eq_l.variants.openai) : type_of% bpl_eq_l :=
  (h.1.trans h.2).symm

end LogspaceDerandomization

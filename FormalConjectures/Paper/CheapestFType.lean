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
# The cheapest F-type Boolean function

An And-Inverter Graph (AIG) is a circuit of two-input AND gates in which every input may be negated.
A Boolean function is *F-type* if it depends on all of its $n$ variables, every size-optimal AIG for
it has at least two gates of fan-out at least two, and its minimum formula size exceeds its minimum
circuit size by exactly one. Let $\mu(n)$ be the least circuit size of an F-type function of $n$
variables.

An edge count gives $\mu(n) \ge n + 1$, and a lift construction gives $\mu(n) \le n + 2$ for every
$n \ge 4$. The source records $\mu(4) = 6$ and $\mu(5) = 7$, obtained by exhaustive enumeration and
SAT computations, and $\mu(6) = 8$, obtained by an exhaustive enumeration that uses no solver and
confirmed class by class by a SAT computation. There is no F-type function of fewer than four
variables. The source conjectures $\mu(n) = n + 2$ for every $n \ge 4$.

*Reference:* [The cheapest F-type function costs n + 2 gates at n = 4, 5, 6](https://doi.org/10.5281/zenodo.23393106)
by Luiz Antonio Busnello (2026).
-/

@[expose] public section

namespace CheapestFType

variable {n : Nat}

/-- An assignment to the $n$ inputs. -/
abbrev Assign (n : Nat) := Fin n → Bool
/-- A Boolean function of $n$ variables. -/
abbrev Func (n : Nat) := Assign n → Bool

/-! ## Essential variables -/

/-- Flips the bit of variable `i` in the assignment `x`. -/
def flipAt (x : Assign n) (i : Fin n) : Assign n :=
  fun j => if j = i then !x j else x j

/-- `f` depends essentially on variable `i`: for some assignment, flipping only
`i` changes the value of `f`. -/
def dependsOn (f : Func n) (i : Fin n) : Prop :=
  ∃ x, f x ≠ f (flipAt x i)

/-! ## AIG circuits

A circuit is a list of gates. Wires `0, …, n - 1` are the variables and wire `n + p` is the
output of gate `p`. The output of the circuit is its last gate. -/

/-- A two-input AND gate. Each input is a wire index and may be negated. -/
structure Gate where
  na : Bool  -- negate input a?
  ia : Nat   -- wire of input a
  nb : Bool
  ib : Nat

/-- Value of wire `i` under the assignment `x`, given the values `vals` of the gates
already evaluated (in evaluation order). -/
def wireVal (x : Assign n) (vals : Array Bool) (i : Nat) : Bool :=
  if h : i < n then x ⟨i, h⟩ else vals.getD (i - n) false

/-- Evaluates the circuit under `x` and returns the array of gate values. -/
def evalGates (x : Assign n) (gs : List Gate) : Array Bool :=
  gs.foldl
    (fun vals g =>
      vals.push ((xor g.na (wireVal x vals g.ia)) && (xor g.nb (wireVal x vals g.ib))))
    #[]

/-- Output value of the circuit (its last gate) under `x`. The empty circuit outputs `false`. -/
def circuitOut (x : Assign n) (gs : List Gate) : Bool :=
  (evalGates x gs).getD (gs.length - 1) false

/-- Well-formedness: each gate reads only earlier wires (inputs `< n` or gates already
computed). -/
def wfC (n : Nat) (gs : List Gate) : Prop :=
  ∀ p : Fin gs.length, (gs.get p).ia < n + p.val ∧ (gs.get p).ib < n + p.val

/-- The circuit computes `f` (output negation is free). -/
def CircuitComputes (gs : List Gate) (f : Func n) : Prop :=
  (∀ x, circuitOut x gs = f x) ∨ (∀ x, circuitOut x gs = !(f x))

/-- `f` has a circuit of at most `k` gates. -/
def HasCircuit (f : Func n) (k : Nat) : Prop :=
  ∃ gs : List Gate, wfC n gs ∧ gs.length ≤ k ∧ CircuitComputes gs f

/-- `m` is the circuit size of `f`: it is attained and it is minimal. -/
def IsOpt (f : Func n) (m : Nat) : Prop :=
  HasCircuit f m ∧ ∀ k, HasCircuit f k → m ≤ k

/-! ## AIG formulas (trees)

Internal nodes are AND gates with free negation on their input edges; leaves are variables or
the constant `1`. Fan-out one is automatic from the tree structure. Output negation is free in
`FormulaComputes`. -/

/-- An AIG formula on $n$ variables. -/
inductive Frm (n : Nat) where
  | var : Fin n → Frm n
  | one : Frm n
  | and : Bool → Frm n → Bool → Frm n → Frm n

/-- The function computed by a formula. -/
def evalF : Frm n → Func n
  | .var i => fun x => x i
  | .one => fun _ => true
  | .and pa a pb b => fun x => (xor pa (evalF a x)) && (xor pb (evalF b x))

/-- The number of AND gates of a formula. -/
def gatesF : Frm n → Nat
  | .var _ => 0
  | .one => 0
  | .and _ a _ b => 1 + gatesF a + gatesF b

/-- The formula computes `f` (output negation is free). -/
def FormulaComputes (φ : Frm n) (f : Func n) : Prop :=
  (evalF φ = f) ∨ (evalF φ = fun x => !(f x))

/-- `f` has a formula of at most `k` gates. -/
def HasFormula (f : Func n) (k : Nat) : Prop :=
  ∃ φ : Frm n, gatesF φ ≤ k ∧ FormulaComputes φ f

/-- `t` is the formula size of `f`. -/
def IsTree (f : Func n) (t : Nat) : Prop :=
  HasFormula f t ∧ ∀ k, HasFormula f k → t ≤ k

/-! ## Fan-out and forced sharing -/

/-- Does gate `g` read wire `w`? -/
def refsWire (g : Gate) (w : Nat) : Bool := g.ia == w || g.ib == w

/-- The fan-out of the gate at position `p`: the number of distinct gates that read its
wire `n + p`. The circuit output does not count. -/
def fanOut (n : Nat) (gs : List Gate) (p : Nat) : Nat :=
  gs.countP (fun g => refsWire g (n + p))

/-- The number of shared gates of a circuit: gates of fan-out at least two. -/
def numReconv (n : Nat) (gs : List Gate) : Nat :=
  (List.range gs.length).countP (fun p => decide (2 ≤ fanOut n gs p))

/-- `f` is *forced-multi*: every well-formed circuit of optimal size that computes `f` has at
least two gates of fan-out at least two. -/
def ForcedMulti (f : Func n) : Prop :=
  ∃ m, IsOpt f m ∧
    ∀ gs : List Gate, wfC n gs → gs.length = m → CircuitComputes gs f →
      2 ≤ numReconv n gs

/-- `Gap f g`: the formula size of `f` exceeds its circuit size by `g`. -/
def Gap (f : Func n) (g : Nat) : Prop :=
  ∃ m t, IsOpt f m ∧ IsTree f t ∧ t = m + g

/-! ## The conjecture -/

/-- `f` is F-type: it depends on all of its $n$ variables, it is forced-multi, and its formula
size exceeds its circuit size by exactly one. -/
def FType (f : Func n) : Prop :=
  (∀ i : Fin n, dependsOn f i) ∧ ForcedMulti f ∧ Gap f 1

/-- For every $n \ge 4$, the least circuit size of an F-type function of $n$ variables is
$n + 2$. -/
@[category research open, AMS 68 94]
theorem ftype_min_eq (n : ℕ) (hn : 4 ≤ n) :
    IsLeast {m : ℕ | ∃ f : Func n, FType f ∧ IsOpt f m} (n + 2) := by
  sorry

/-- Every F-type function of $n \ge 4$ variables has circuit size at least $n + 2$.
Together with the lift construction, this is equivalent to `ftype_min_eq`. -/
@[category research open, AMS 68 94]
theorem ftype_opt_ge (n : ℕ) (hn : 4 ≤ n) (f : Func n) (m : ℕ)
    (hf : FType f) (hm : IsOpt f m) : n + 2 ≤ m := by
  sorry

/-- A forced-multi function with $n \ge 4$ essential variables and circuit size $n + 1$ has
formula size at least $n + 3$. The source shows that this is equivalent to `ftype_opt_ge`. -/
@[category research open, AMS 68 94]
theorem forcedMulti_tree_ge (n : ℕ) (hn : 4 ≤ n) (f : Func n) (t : ℕ)
    (hess : ∀ i : Fin n, dependsOn f i) (hfm : ForcedMulti f)
    (hopt : IsOpt f (n + 1)) (htree : IsTree f t) : n + 3 ≤ t := by
  sorry

/-- The edge-count bound: a forced-multi function with $n$ essential variables has circuit size
at least $n + 1$. -/
@[category research solved, AMS 68 94]
theorem forcedMulti_opt_ge (f : Func n) (m : ℕ)
    (hess : ∀ i : Fin n, dependsOn f i) (hfm : ForcedMulti f) (hopt : IsOpt f m) :
    n + 1 ≤ m := by
  sorry

/-! ## Tests for the definitions -/

/-- The empty circuit computes every constant function. -/
@[category test, AMS 68 94]
theorem hasCircuit_zero_of_const (f : Func n) (c : Bool) (hc : ∀ x, f x = c) :
    HasCircuit f 0 := by
  refine ⟨[], fun p => absurd p.isLt (by simp), Nat.le_refl _, ?_⟩
  cases c with
  | false => exact Or.inl (fun x => by rw [hc x]; rfl)
  | true => exact Or.inr (fun x => by rw [hc x]; rfl)

/-- Constant functions are never forced-multi. In particular there is no F-type function of `0`
variables. -/
@[category test, AMS 68 94]
theorem not_forcedMulti_of_const (f : Func n) (c : Bool) (hc : ∀ x, f x = c) :
    ¬ ForcedMulti f := by
  intro ⟨m, hopt, hall⟩
  have h0 := hasCircuit_zero_of_const f c hc
  have hm : m = 0 := Nat.le_zero.mp (hopt.2 0 h0)
  subst hm
  have h2 := hall [] (fun p => absurd p.isLt (by simp)) rfl
  have hc' : CircuitComputes ([] : List Gate) f := by
    obtain ⟨gs, _, hle, hcc⟩ := hopt.1
    have : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst this; exact hcc
  have := h2 hc'
  simp [numReconv] at this

end CheapestFType

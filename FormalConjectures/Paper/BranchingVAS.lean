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
import FormalConjecturesUtil

/-!
# Decidability of reachability for branching vector addition systems

A *branching vector addition system* (BVAS) of dimension `d` is given by a finite
list of *axioms*, a finite list of *unary rules*, and a finite list of *binary
rules*, each of which is a vector in `ℤ^d`. A *configuration* is a vector in `ℕ^d`,
which here is represented as a vector `v ∈ ℤ^d` subject to `0 ≤ v`. The set of
*reachable* configurations is defined inductively:

* every axiom that is a valid configuration (i.e. lies in `ℕ^d`) is reachable;
* if `v` is a reachable configuration, `r` is a unary rule and `v + r ∈ ℕ^d`, then
  `v + r` is reachable;
* if `v₁, v₂` are both reachable configurations, `r` is a binary rule and
  `v₁ + v₂ + r ∈ ℕ^d`, then `v₁ + v₂ + r` is reachable.

Modelling axioms as vectors in `ℤ^d` and only counting the non-negative ones as
reachable yields the same set of reachable configurations as the usual definition
in which axioms are required to lie in `ℕ^d`.

Branching vector addition systems are distinguished from ordinary vector addition systems (VAS) by allowing binary rules. VAS reachability is known to be decidable.

*References:*
- [The covering and boundedness problems for branching vector addition systems](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2009.2317)
  (*Stéphane Demri, Marcin Jurdziński, Oded Lachish, Ranko Lazić*, FSTTCS 2009)
  Gives a similar definition of BVAS, and compares it to related equivalent definitions.
- [On the Reachability Problem for Two-Dimensional Branching VASS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.22)
  by *Clotilde Bizière, Thibault Hilaire, Jérôme Leroux, Grégoire Sutre*, MFCS 2025, which
  settles the two-dimensional case and states that "the decidability status of the reachability
  problem for BVASS remains open in higher dimensions".
- [The General Vector Addition System Reachability Problem by Presburger Inductive
  Invariants](https://arxiv.org/abs/1009.1076) by *Jérôme Leroux* (2010), for the decidability
  of reachability for ordinary VAS.
- [Solving the Reachability Problem for Branching Vector Addition Systems via Semilinear
  Inductive Invariants](https://arxiv.org/abs/2607.09558) by *Clotilde Bizière, Jérôme Leroux,
  Grégoire Sutre* (2026), a recent preprint claiming a positive resolution to the conjecture:
  reachability for branching vector addition systems is decidable.
-/

namespace BranchingVAS

/--
A branching vector addition system of dimension `d`.
-/
structure Bvas (d : ℕ) where
  axioms : List (Fin d → ℤ)
  unaryRules : List (Fin d → ℤ)
  binaryRules : List (Fin d → ℤ)

/-- The reachable configurations of a branching vector addition system. -/
inductive Bvas.Reachable {d : ℕ} (b : Bvas d) : (Fin d → ℤ) → Prop
  | base {v : Fin d → ℤ} (hmem : v ∈ b.axioms) (hcfg : 0 ≤ v) : b.Reachable v
  | unary {v r w : Fin d → ℤ} (hv : b.Reachable v) (hr : r ∈ b.unaryRules)
      (hcfg : 0 ≤ w) (hw : w = v + r) : b.Reachable w
  | binary {v₁ v₂ r w : Fin d → ℤ} (hv₁ : b.Reachable v₁) (hv₂ : b.Reachable v₂)
      (hr : r ∈ b.binaryRules) (hcfg : 0 ≤ w) (hw : w = v₁ + v₂ + r) : b.Reachable w

/--
The vector in `ℤ^d` whose `i`-th coordinate is the `i`-th entry of the list `l`, or `0` if `l`
has fewer than `i + 1` entries. Used to encode the inputs of the reachability problem.
-/
def vecOfList (d : ℕ) (l : List ℤ) : Fin d → ℤ := fun i => l.getD i 0

@[category API, AMS 3 68]
theorem vecOfList_ofFn {d : ℕ} (v : Fin d → ℤ) : vecOfList d (List.ofFn v) = v := by
  funext i
  simp [vecOfList, List.getD_eq_getElem?_getD]

@[category API, AMS 3 68]
theorem ofFn_vecOfList (d : ℕ) (l : List ℤ) :
    List.ofFn (vecOfList d l) = (List.range d).map fun i => l.getD i 0 := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

@[category API, AMS 3 68]
theorem primrec_ofFn_vecOfList : Primrec₂ fun d l => List.ofFn (vecOfList d l) :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    ((Primrec.list_getD 0).comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
      fun ⟨d, l⟩ => (ofFn_vecOfList d l).symm

/--
An input of the reachability problem, that is, a dimension `d`, a branching vector addition
system of dimension `d` and a target vector in `ℤ^d`, is encoded by `d` together with the lists
of entries of the axioms, of the rules and of the target.
-/
instance : Primcodable (Σ d : ℕ, Bvas d × (Fin d → ℤ)) :=
  Primcodable.ofLeftInverse
    (fun p => (p.1, p.2.1.axioms.map List.ofFn, p.2.1.unaryRules.map List.ofFn,
      p.2.1.binaryRules.map List.ofFn, List.ofFn p.2.2))
    (fun q => ⟨q.1, ⟨q.2.1.map (vecOfList q.1), q.2.2.1.map (vecOfList q.1),
      q.2.2.2.1.map (vecOfList q.1)⟩, vecOfList q.1 q.2.2.2.2⟩)
    (fun p => by simp [List.map_map, Function.comp_def, vecOfList_ofFn])
    (by
      have h : Primrec fun q : ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ =>
          (q.1, q.2.1.map fun l => List.ofFn (vecOfList q.1 l),
            q.2.2.1.map fun l => List.ofFn (vecOfList q.1 l),
            q.2.2.2.1.map fun l => List.ofFn (vecOfList q.1 l),
            List.ofFn (vecOfList q.1 q.2.2.2.2)) :=
        Primrec.pair Primrec.fst <| Primrec.pair (Primrec.list_map (Primrec.fst.comp Primrec.snd)
            (primrec_ofFn_vecOfList.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)) <|
          Primrec.pair (Primrec.list_map (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
            (primrec_ofFn_vecOfList.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)) <|
          Primrec.pair
            (Primrec.list_map
              (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
              (primrec_ofFn_vecOfList.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))
            (primrec_ofFn_vecOfList.comp Primrec.fst
              (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd))
      exact h.of_eq fun q => by simp [List.map_map, Function.comp_def])

/--
The reachability problem for branching vector addition systems is decidable.

That is, the predicate taking a dimension `d`, a branching vector addition system `b` of
dimension `d` and a target vector `t ∈ ℤ^d`, and returning whether `t` is reachable in `b`, is
a computable predicate. Note that the dimension is part of the input: a single algorithm must
work for all dimensions.

As of August 2026, the solution is quite recently announced and is not
yet peer-reviewed.
-/
@[category research solved, AMS 3 68]
theorem reachability_decidable :
    ComputablePred fun p : Σ d : ℕ, Bvas d × (Fin d → ℤ) => p.2.1.Reachable p.2.2 := by
  sorry

/-- Every axiom that is non-negative is reachable. -/
@[category test, AMS 3 68]
theorem reachable_of_mem_axioms {d : ℕ} (b : Bvas d) {v : Fin d → ℤ}
    (hmem : v ∈ b.axioms) (hcfg : 0 ≤ v) : b.Reachable v :=
  .base hmem hcfg

/-- Reachable vectors are always non-negative. -/
@[category test, AMS 3 68]
theorem reachable_imp_pos {d : ℕ} (v : Fin d → ℤ) (b : Bvas d) :
    b.Reachable v → 0 ≤ v := by
  intro h; cases h; all_goals assumption

/-- A small BVAS of dimension 3 used for a test below. -/
def exampleBvas : Bvas 3 := {
  axioms := [![3,1,0], ![0,0,0]],
  unaryRules := [![1,-10,-10], ![-1,0,1]],
  binaryRules := [![-1,-1,10]],
}

/--
A small (indeed, degenerate, since it contains no binary rules) BVAS of
dimension 2 used for a test below.
-/
def exampleBvas2 : Bvas 2 := {
  axioms := [![10,0]],
  unaryRules := [![-1, 1]],
  binaryRules := [],
}

/--
The vector [0, 0, 12] is reachable in the first example BVAS.
-/
@[category test, AMS 3 68]
theorem reachable_example : exampleBvas.Reachable ![0,0,12] :=
  have h1 : exampleBvas.Reachable ![3,1,0] := .base
    (by decide)
    (by intro i; fin_cases i <;> simp)
  have h2 : exampleBvas.Reachable ![0,0,0] := .base
    (by decide)
    (by intro i; fin_cases i <;> simp)
  have h3 : exampleBvas.Reachable ![2,0,10] := by
    refine .binary (r := ![-1, -1, 10]) h1 h2 (by decide) ?_ (by decide)
    intro i; fin_cases i <;> simp
  have h4 : exampleBvas.Reachable ![1,0,11] := by
    refine .unary  (r := ![-1, 0, 1]) h3 (by decide) ?_ (by decide)
    intro i; fin_cases i <;> simp
  have h5 : exampleBvas.Reachable ![0,0,12] := by
    refine .unary (r := ![-1, 0, 1]) h4 (by decide) ?_ (by decide)
    intro i; fin_cases i <;> simp
  h5

/--
The vector [0, 0] is not reachable in the second example BVAS.
-/
@[category test, AMS 3 68]
theorem not_reachable_example : ¬ exampleBvas2.Reachable ![0,0] := by
  let rec invariant (v : Fin 2 → ℤ) :
      (hv : exampleBvas2.Reachable v) → v 0 + v 1 = 10
    | .base hmem hcfg => by fin_cases hmem; simp
    | .unary hv hr hcfg hw => by
        fin_cases hr;
        · rw [hw]
          simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
          ring_nf
          exact invariant _ hv
    | .binary _ _ hr _ _ => by fin_cases hr
  intro h
  simpa using invariant _ h

end BranchingVAS

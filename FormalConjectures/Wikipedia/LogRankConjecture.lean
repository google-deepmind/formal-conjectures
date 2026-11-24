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
# The log-rank conjecture

For a finite two-party Boolean function $f : X \times Y \to \mathrm{Bool}$, let $D(f)$ denote its
deterministic communication complexity and let $M_f$ denote its $\{0, 1\}$-valued matrix over
$\mathbb{R}$. Monochromatic rectangle decomposition yields
$D(f) \ge \log_2 \operatorname{rank}_{\mathbb{R}}(M_f)$ whenever $f$ is not identically false.

Lovász and Saks [LS88] conjectured that $D(f)$ is bounded above by a polynomial in
$\log_2 \operatorname{rank}_{\mathbb{R}}(M_f)$. Lovett [Lo16] established
$D(f) = O(\sqrt{\operatorname{rank}(M_f)} \log_2 \operatorname{rank}(M_f))$, and Sudakov and Tomon
[ST23] removed the logarithmic factor to obtain $D(f) = O(\sqrt{\operatorname{rank}(M_f)})$.

*References:*
- [Wikipedia: Log-rank conjecture](https://en.wikipedia.org/wiki/Log-rank_conjecture)
- [LS88] L. Lovász, M. Saks, *Lattices, Möbius functions and communication complexity*, in
  *Proceedings of the 29th Annual Symposium on Foundations of Computer Science (FOCS 1988)*, IEEE,
  1988, pp. 81–90.
- [Lo16] S. Lovett, *Communication is bounded by root of rank*, J. ACM **63** (2016), no. 1,
  Article 1, 1–9, https://doi.org/10.1145/2724704.
- [ST23] B. Sudakov, I. Tomon, *Matrix discrepancy and the log-rank conjecture*,
  [arXiv:2311.18524](https://arxiv.org/abs/2311.18524) (2023).
-/

@[expose] public section

namespace LogRankConjecture

/-- A deterministic two-party communication protocol tree on domains `X` and `Y` with Boolean
output. At each internal step, either the first party sends one bit (`sendLeft`) or the second
party sends one bit (`sendRight`). -/
inductive Protocol (X Y : Type*) : Type _
  | leaf (b : Bool) : Protocol X Y
  | sendLeft (f : X → Bool) (next : Bool → Protocol X Y) : Protocol X Y
  | sendRight (g : Y → Bool) (next : Bool → Protocol X Y) : Protocol X Y

/-- Evaluates a deterministic communication protocol `P` on input `(x, y)`. -/
def Protocol.eval {X Y : Type*} : Protocol X Y → X → Y → Bool
  | .leaf b, _, _ => b
  | .sendLeft f next, x, y => (next (f x)).eval x y
  | .sendRight g next, x, y => (next (g y)).eval x y

/-- Worst-case number of bits exchanged (tree depth) in a deterministic protocol `P`. -/
def Protocol.depth {X Y : Type*} : Protocol X Y → ℕ
  | .leaf _ => 0
  | .sendLeft _ next => 1 + max (next false).depth (next true).depth
  | .sendRight _ next => 1 + max (next false).depth (next true).depth

/-- Deterministic communication complexity $D(f)$ of $f : X \to Y \to \mathrm{Bool}$, defined as
the least depth of a protocol tree computing $f$. -/
noncomputable def detCommComplexity {X Y : Type*} (f : X → Y → Bool) : ℕ :=
  sInf {d : ℕ | ∃ P : Protocol X Y, P.eval = f ∧ P.depth ≤ d}

/-- Real $\{0, 1\}$-matrix $M_f$ associated with $f : X \to Y \to \mathrm{Bool}$. -/
def commMatrix {X Y : Type*} (f : X → Y → Bool) : Matrix X Y ℝ :=
  fun x y => if f x y then 1 else 0

/-- Every constant Boolean function has deterministic communication complexity `0`. -/
@[category API, AMS 15 68 94]
theorem detCommComplexity_const {X Y : Type*} (b : Bool) :
    detCommComplexity (fun (_ : X) (_ : Y) => b) = 0 := by
  unfold detCommComplexity
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨.leaf b, rfl, le_rfl⟩)

/-- On `Bool × Bool`, the left projection `(x, y) ↦ x` has exact communication complexity `1`. -/
@[category test, AMS 15 68 94]
theorem detCommComplexity_fst_eq_one :
    detCommComplexity (fun (x _ : Bool) => x) = 1 := by
  have hle : detCommComplexity (fun (x _ : Bool) => x) ≤ 1 := by
    unfold detCommComplexity
    apply Nat.sInf_le
    refine ⟨.sendLeft id (fun b => .leaf b), ?_, ?_⟩
    · ext x y
      simp [Protocol.eval]
    · simp [Protocol.depth]
  have hne : detCommComplexity (fun (x _ : Bool) => x) ≠ 0 := by
    unfold detCommComplexity
    intro h
    rcases Nat.sInf_eq_zero.mp h with ⟨P, hP, hdepth⟩ | hempty
    · cases P with
      | leaf b =>
        have h0 := congr_fun (congr_fun hP false) false
        have h1 := congr_fun (congr_fun hP true) false
        simp [Protocol.eval] at h0 h1
        subst h0
        exact Bool.false_ne_true h1
      | sendLeft _ _ =>
        simp [Protocol.depth] at hdepth
      | sendRight _ _ =>
        simp [Protocol.depth] at hdepth
    · have hmem : 1 ∈ {d : ℕ | ∃ P : Protocol Bool Bool,
          P.eval = (fun x _ => x) ∧ P.depth ≤ d} := by
        refine ⟨.sendLeft id (fun b => .leaf b), ?_, ?_⟩
        · ext x y
          simp [Protocol.eval]
        · simp [Protocol.depth]
      rw [hempty] at hmem
      exact hmem
  omega

/-- The communication matrix of the identically-false function has real rank `0`. -/
@[category test, AMS 15 68 94]
theorem commMatrix_const_false_rank {X Y : Type*} [Fintype X] [Fintype Y] :
    (commMatrix (fun (_ : X) (_ : Y) => false)).rank = 0 := by
  have h : commMatrix (fun (_ : X) (_ : Y) => false) = 0 := by
    ext x y
    simp [commMatrix]
  rw [h, Matrix.rank_zero]

/--
**Log-rank lower bound**: for every finite two-party Boolean function $f$ that takes the value
`true` at least once, $\log_2 \operatorname{rank}_{\mathbb{R}}(M_f) \le D(f)$.
-/
@[category textbook, AMS 15 68 94]
theorem log_lower_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (hf : ∃ x y, f x y = true) :
    Real.logb 2 (commMatrix f).rank ≤ (detCommComplexity f : ℝ) := by
  sorry

/--
**Lovett's root-rank bound** [Lo16]: there exists an absolute constant $C > 0$ such that every
finite two-party Boolean function $f$ satisfies
$$D(f) \le C \sqrt{\operatorname{rank}_{\mathbb{R}}(M_f)}
  \log_2 \operatorname{rank}_{\mathbb{R}}(M_f) + C.$$
The additive $+ C$ term absorbs the degenerate cases $\operatorname{rank}_{\mathbb{R}}(M_f) \le 1$,
where $\log_2 \operatorname{rank}_{\mathbb{R}}(M_f) = 0$ and $D(f) \le 2$.
-/
@[category research solved, AMS 15 68 94]
theorem lovett_root_rank_bound :
    ∃ C > (0 : ℝ), ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
      (detCommComplexity f : ℝ) ≤
        C * Real.sqrt (commMatrix f).rank * Real.logb 2 (commMatrix f).rank + C := by
  sorry

/--
**Sudakov–Tomon bound** [ST23]: there exists an absolute constant $C > 0$ such that every finite
two-party Boolean function $f$ satisfies
$D(f) \le C \sqrt{\operatorname{rank}_{\mathbb{R}}(M_f)} + C$.
-/
@[category research solved, AMS 15 68 94]
theorem sudakov_tomon_root_rank_bound :
    ∃ C > (0 : ℝ), ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
      (detCommComplexity f : ℝ) ≤ C * Real.sqrt (commMatrix f).rank + C := by
  sorry

/--
**The log-rank conjecture** [LS88]: there exist universal constants $C > 0$ and $c > 0$ such that
every finite two-party Boolean function $f$ satisfies
$D(f) \le C (\log_2 \operatorname{rank}_{\mathbb{R}}(M_f))^c + C$.
The additive $+ C$ term handles $\operatorname{rank}_{\mathbb{R}}(M_f) \le 1$, where
$\log_2 \operatorname{rank}_{\mathbb{R}}(M_f) = 0$ and $D(f) \le 2$.
-/
@[category research open, AMS 15 68 94]
theorem log_rank_conjecture :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
      (detCommComplexity f : ℝ) ≤ C * (Real.logb 2 (commMatrix f).rank) ^ c + C := by
  sorry

end LogRankConjecture

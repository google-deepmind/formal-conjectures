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
# Erdős Problem 1205

*References:*
- [erdosproblems.com/1205](https://www.erdosproblems.com/1205)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115. [PDF](https://www.renyi.hu/~p_erdos/1980-03.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1205

/-- A choice of one congruence class for each modulus $n\in\{1,\ldots,x\}$. The index
`i : Fin x` stands for the modulus $n=i+1$, and `a i : Fin (i + 1)` is the residue $a_n \bmod n$
chosen for it. -/
abbrev Assignment (x : ℕ) := (i : Fin x) → Fin (i.1 + 1)

/-- `Covers a m i` says that the integer $m+1\in\{1,\ldots,x\}$ satisfies the congruence chosen
for the modulus $i+1$, that is, $m+1\equiv a_{i+1} \pmod{i+1}$ (see `covers_iff_modEq`). -/
def Covers {x : ℕ} (a : Assignment x) (m i : Fin x) : Prop :=
  (m.1 + 1) % (i.1 + 1) = (a i).1

/-- The number of chosen congruences satisfied by the integer $m+1\in\{1,\ldots,x\}$. -/
noncomputable def coverage {x : ℕ} (a : Assignment x) (m : Fin x) : ℕ :=
  open scoped Classical in
  ((Finset.univ : Finset (Fin x)).filter fun i ↦ Covers a m i).card

/-- `IsCovering x k` says that some choice of congruence classes, one for each modulus
$n\le x$, makes every integer $m\in\{1,\ldots,x\}$ satisfy at least `k` of the congruences.
The clause `k ≤ x` is automatic for `x ≥ 1`, since an integer satisfies at most `x` of the
congruences; it only forces `k = 0` when `x = 0`. -/
def IsCovering (x k : ℕ) : Prop :=
  k ≤ x ∧ ∃ a : Assignment x, ∀ m : Fin x, k ≤ coverage a m

/-- $F(x)$: the largest `k ≤ x` with `IsCovering x k`. Since `IsCovering x 0` always holds,
`Nat.findGreatest` never returns its default value `0` for lack of a witness. For `x ≥ 1` this
is the maximum of `k` such that some choice of classes covers every $m\le x$ at least `k` times,
and $F(0)=0$. -/
noncomputable def F (x : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (IsCovering x) x

/-- The encoding of `Covers` is the congruence $m+1\equiv a_{i+1}\pmod{i+1}$. -/
@[category API, AMS 11]
theorem covers_iff_modEq {x : ℕ} (a : Assignment x) (m i : Fin x) :
    Covers a m i ↔ (m.1 + 1) ≡ (a i).1 [MOD i.1 + 1] := by
  unfold Covers Nat.ModEq
  rw [Nat.mod_eq_of_lt (a i).2]

/-- With no moduli and no integers to cover, $F(0)=0$. -/
@[category API, AMS 11]
theorem F_zero : F 0 = 0 := by
  classical
  exact Nat.findGreatest_zero

/-- The answer: $F(x)\sim\log x$. -/
noncomputable def erdos_1205.answer (x : ℕ) : ℝ := Real.log x

/--
Let $F(x)$ be maximal such that there exists, for all $n\leq x$, a congruence class
$a_n\pmod{n}$ such that every $m\leq x$ satisfies at least $F(x)$ of these congruences.

Estimate $F(x)$.

Erdős [Er80, p. 108] describes $F(x)\to\infty$ as a simple exercise and asks how fast $F(x)$
tends to infinity. The estimate $F(x)\sim\log x$ comes from the argument given on
erdosproblems.com/1205 (a pigeonhole upper bound and a probabilistic lower bound), not from a
paper.
-/
@[category research solved, question value, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1205.lean#L1065"]
theorem erdos_1205 : (fun x : ℕ ↦ (F x : ℝ)) ~[atTop] erdos_1205.answer := by
  sorry

/--
The pigeonhole principle implies $F(x)\leq \sum_{n\leq x}\frac{1}{n}= \log x+O(1)$.

We state the exact pigeonhole bound $F(x)\leq H_x+1$, where $H_x=\sum_{n\leq x}\frac{1}{n}$ is
the $x$-th harmonic number. The $+1$ is needed, since $F(3)\geq 2>H_3$. By Mathlib's
`harmonic_le_one_add_log` this gives $F(x)\leq\log x+2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1205.lean#L235"]
theorem erdos_1205.variants.upper_bound (x : ℕ) : (F x : ℝ) ≤ (harmonic x : ℝ) + 1 := by
  sorry

end Erdos1205

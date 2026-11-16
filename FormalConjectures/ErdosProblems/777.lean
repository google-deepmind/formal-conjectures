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
# Erdős Problem 777

*References:*
- [erdosproblems.com/777](https://www.erdosproblems.com/777)
- [Gu83] Guy, R. K., *A miscellany of Erdős problems*. Amer. Math. Monthly (1983), 118-120.
- [AlFr85] Alon, N. and Frankl, P., *The maximum number of disjoint pairs in a family of
  subsets*. Graphs Combin. (1985), 13-21.
- [ADGS15] Alon, N., Das, S., Glebov, R. and Sudakov, B., *Comparable pairs in families of
  sets*. J. Combin. Theory Ser. B (2015), 164-185. [arXiv](https://arxiv.org/abs/1411.4196)
-/

@[expose] public section

namespace Erdos777

/-- The comparability graph $G_{\mathcal{F}}$ of a finite family $\mathcal{F}$ of subsets of
$\{1,\ldots,n\}$ (modelled by `Fin n`): its vertices are the members of $\mathcal{F}$, and two
members are adjacent when one is a proper subset of the other (equivalently, they are distinct
and comparable; a graph has no loops). -/
def comparableGraph {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : SimpleGraph {A // A ∈ 𝓕} where
  Adj A B := A.1 < B.1 ∨ B.1 < A.1
  symm := ⟨by intro A B; tauto⟩
  loopless := ⟨by intro A h; exact (lt_irrefl A.1) (h.elim id id)⟩

/-- Two members of $\mathcal{F}$ are adjacent in `comparableGraph 𝓕` if and only if one is a
proper subset of the other. -/
@[category API, AMS 5]
theorem comparableGraph_adj {n : ℕ} {𝓕 : Finset (Finset (Fin n))} {A B : {S // S ∈ 𝓕}} :
    (comparableGraph 𝓕).Adj A B ↔ A.1 < B.1 ∨ B.1 < A.1 :=
  Iff.rfl

open scoped Classical in
/-- The number of edges of $G_{\mathcal{F}}$, i.e. of unordered pairs of distinct comparable
members of $\mathcal{F}$. -/
noncomputable def comparableEdges {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : ℕ :=
  (comparableGraph 𝓕).edgeFinset.card

set_option linter.style.formal_proof_palomar false in
/--
If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ then we write $G_{\mathcal{F}}$ for the
graph on $\mathcal{F}$ where $A\sim B$ if $A$ and $B$ are comparable - that is, $A\subseteq B$ or
vice versa.

Is it true that, if $\epsilon>0$ and $n$ is sufficiently large, whenever
$m\leq (2-\epsilon)2^{n/2}$ the graph $G_\mathcal{F}$ has $<2^{n}$ many edges?

A problem of Daykin and Erdős [Gu83]; here $m=\lvert\mathcal{F}\rvert$. The answer is yes, which
follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov, and Sudakov [ADGS15].
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos777.lean#L1759"]
theorem erdos_777.parts.i :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) → comparableEdges 𝓕 < 2 ^ n := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ then we write $G_{\mathcal{F}}$ for the
graph on $\mathcal{F}$ where $A\sim B$ if $A$ and $B$ are comparable - that is, $A\subseteq B$ or
vice versa.

Is it true that if $G_{\mathcal{F}}$ has $\geq cm^2$ edges then $m\ll_c 2^{n/2}$?

The answer is no, by Alon and Frankl [AlFr85, Example 6.1]: for every $d\geq 1$ there are
families with $m\gg n^d2^{n/2}$ and at least $2^{-2d-1}\binom{m}{2}$ comparable pairs. Here
$m=\lvert\mathcal{F}\rvert$, and the question is read as: for every $c>0$ there is $C=C(c)$ such
that $m\leq C2^{n/2}$ for all $n$ and all such families, so the answer is the negation.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos777.lean#L353"]
theorem erdos_777.parts.ii :
    ¬ ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      c * (𝓕.card : ℝ) ^ 2 ≤ comparableEdges 𝓕 →
        (𝓕.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ then we write $G_{\mathcal{F}}$ for the
graph on $\mathcal{F}$ where $A\sim B$ if $A$ and $B$ are comparable - that is, $A\subseteq B$ or
vice versa.

Is it true that, for any $\epsilon>0$, there exists some $\delta>0$ such that if there are
$>m^{2-\delta}$ edges then $m<(2+\epsilon)^{n/2}$?

The answer is yes, proved by Alon and Frankl [AlFr85, Theorem 1.4, the case $k=1$]. Here
$m=\lvert\mathcal{F}\rvert$.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos777.lean#L945"]
theorem erdos_777.parts.iii :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ^ (2 - δ) < comparableEdges 𝓕 →
        (𝓕.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2) := by
  sorry

end Erdos777

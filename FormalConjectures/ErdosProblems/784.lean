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
/-
Definitions adapted from the external formalization by OpenAI Codex.
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under the Apache 2.0 license. This file has been modified.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 784

*References:*
- [erdosproblems.com/784](https://www.erdosproblems.com/784)
- [Ru82] Ruzsa, Imre Z., _On the small sieve. II. Sifting by composite numbers_.
  J. Number Theory (1982), 260–268.
- [We25] Weingartner, Andreas, _The Schinzel-Szekeres function_.
  Res. Number Theory (2025), Paper No. 63, 32.
- [External Lean proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos784.lean)
-/

@[expose] public section

namespace Erdos784

/-- The reciprocal mass of a finite set of natural numbers. -/
noncomputable def reciprocalMass (A : Finset ℕ) : ℝ := ∑ a ∈ A, (a : ℝ)⁻¹

/-- The positive integers at most $N$ divisible by no member of $A$. -/
noncomputable def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

/-- The hypotheses as printed, allowing $1 \in A$. -/
def LiteralAdmissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ reciprocalMass A ≤ C

/-- The intended hypotheses, excluding the trivial obstruction $1 \in A$. -/
def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 N ∧ reciprocalMass A ≤ C

/-- A uniform polynomial-logarithmic lower bound; the constants may depend on $C$. -/
def HasPolylogLowerBound
    (admissible : ℝ → ℕ → Finset ℕ → Prop) (C : ℝ) : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, admissible C N A →
      K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c ≤ (unsieved N A).card

/-- The lower bound for the literal formulation. -/
def LiteralAnswer : ℝ → Prop := HasPolylogLowerBound LiteralAdmissible

/-- The lower bound for the formulation with $1 \notin A$. -/
def CorrectedAnswer : ℝ → Prop := HasPolylogLowerBound Admissible

/--
Let $C>0$. Does there exist a $c>0$ (depending on $C$) such that, for all sufficiently
large $x$, if $A\subseteq [1,x]$ has $\sum_{n\in A}\frac{1}{n}\leq C$ then
$$\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}\gg\frac{x}{(\log x)^c}?$$

The answer as printed is no: $A=\{1\}$ is a counterexample for every $C\geq 1$.
The intended restriction $1\notin A$ is treated by the corrected classification below.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos784.lean#L1762"]
theorem erdos_784 : ¬ ∀ C : ℝ, 0 < C → LiteralAnswer C := by sorry

/-- For positive $C$, the literal lower bound holds precisely when $C<1$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos784.lean#L1762"]
theorem erdos_784.variants.literal_classification {C : ℝ} (hC : 0 < C) :
    LiteralAnswer C ↔ C < 1 := by sorry

/--
With $1\notin A$, the lower bound holds precisely when $0<C\leq 1$.
For fixed $C>1$ Ruzsa answered this question in the negative.
The case $C<1$ follows from the union bound; the endpoint $C=1$ is due to Ruzsa [Ru82].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos784.lean#L1722"]
theorem erdos_784.variants.corrected_classification {C : ℝ} (hC : 0 < C) :
    CorrectedAnswer C ↔ C ≤ 1 := by sorry

end Erdos784


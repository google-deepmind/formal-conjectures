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
# Erdős Problem 300

*References:*
- [erdosproblems.com/300](https://www.erdosproblems.com/300)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
- [Cr03] Croot, III, Ernest S., *On a coloring conjecture about unit fractions*. Ann. of Math. (2)
  (2003), 545-556.
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  arXiv:2404.07113 (2024).
-/

@[expose] public section

open Filter Topology

namespace Erdos300

/-- $A(N)$ is the maximal cardinality of $A\subseteq \{1,\ldots,N\}$ such that
$\sum_{n\in S}\frac{1}{n}\neq 1$ for all $S\subseteq A$. -/
noncomputable def A (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ (∀ S ⊆ B, ∑ n ∈ S, (1 / n : ℚ) ≠ 1) ∧
    B.card = m}

/--
Let $A(N)$ denote the maximal cardinality of $A\subseteq \{1,\ldots,N\}$ such that
$\sum_{n\in S}\frac{1}{n}\neq 1$ for all $S\subseteq A$. Estimate $A(N)$.

Erdős and Graham [ErGr80] believe the answer is $A(N)=(1+o(1))N$. Croot [Cr03] disproved this,
showing the existence of some constant $c<1$ such that $A(N)<cN$ for all large $N$. It is
trivial that $A(N)\geq (1-\frac{1}{e}+o(1))N$. Liu and Sawhney [LiSa24] have proved that
$A(N)=(1-1/e+o(1))N$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos300.lean#L4356"]
theorem erdos_300 : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 (1 - 1 / Real.exp 1)) := by
  sorry

/-- Erdős and Graham [ErGr80] believed that $A(N)=(1+o(1))N$; this was disproved by Croot
[Cr03]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos300.lean#L4356"]
theorem erdos_300.variants.erdos_graham : answer(False) ↔
    Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 1) := by
  sorry

end Erdos300

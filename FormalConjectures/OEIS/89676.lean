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
# Maximum size of an acute set in $\{0, 1\}^n$

The sequence $a(n)$ is the maximum number of vertices of the $n$-dimensional hypercube
$\{0, 1\}^n$ such that every three distinct points form a triangle with strictly acute angles
(equivalently, no three distinct points $P, Q, R$ satisfy $(P - Q) \cdot (R - Q) = 0$, or no
three distinct subsets $P, Q, R \subseteq \{0, \dots, n-1\}$ satisfy $P \cap R \subseteq Q \subseteq P \cup R$).

*References:*
- [A089676](https://oeis.org/A089676)
- [EF83] Paul Erdős and Zoltán Füredi,
  [The greatest angle among $n$ points in the $d$-dimensional Euclidean space](https://doi.org/10.1016/S0304-0208(08)73489-3),
  *North-Holland Mathematics Studies* **75** (1983), 275–283.
- [Be06] David Bevan,
  [Sets of points determining only acute angles and some related colouring problems](https://doi.org/10.37236/1038),
  *The Electronic Journal of Combinatorics* **13** (2006), #R12.
- [Ha11] Viktor Harangi,
  [Acute sets in Euclidean spaces](https://doi.org/10.1137/100807234),
  *SIAM Journal on Discrete Mathematics* **25** (2011), 1212–1229.
- [Su26a] Mar Allen P. Sugui,
  [Formal Verification and Lower-Bound Records for Cubic Acute Sets (OEIS A089676) in Lean 4](https://doi.org/10.5281/zenodo.24210870),
  2026.
- [Su26b] Mar Allen P. Sugui,
  [Exactness at Dimension 8, Harangi $s=3$ Compositions, and Extended Lower-Bound Records for Cubic Acute Sets (OEIS A089676) in Lean 4](https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/docs/cubic-acute-sets-ii/cubic-acute-sets-ii.pdf),
  2026.
-/

@[expose] public section

namespace OeisA89676

open Finset

/-- A finite subset $S$ of the $n$-dimensional Boolean hypercube (`Finset (Fin n)`) is acute if no
three pairwise distinct elements $P, Q, R \in S$ satisfy $P \cap R \subseteq Q \subseteq P \cup R$
(equivalently, their indicator vectors in $\{0, 1\}^n$ determine no right or obtuse angle). -/
def IsAcute {n : ℕ} (S : Finset (Finset (Fin n))) : Prop :=
  ∀ P ∈ S, ∀ Q ∈ S, ∀ R ∈ S, P ≠ Q → Q ≠ R → P ≠ R →
    ¬ (P ∩ R ⊆ Q ∧ Q ⊆ P ∪ R)

instance {n : ℕ} (S : Finset (Finset (Fin n))) : Decidable (IsAcute S) := by
  unfold IsAcute
  infer_instance

/-- Maximum cardinality of an acute subset of the $n$-dimensional hypercube $\{0, 1\}^n$. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n))).powerset.filter IsAcute).sup card

@[category test, AMS 5 52]
theorem a_0 : a 0 = 1 := by
  decide

@[category test, AMS 5 52]
theorem a_1 : a 1 = 2 := by
  decide

@[category test, AMS 5 52]
theorem a_2 : a 2 = 2 := by
  decide

set_option linter.style.formal_proof_palomar false in
/--
Exact values of $a(n)$ for $0 \le n \le 8$:
$a(0) = 1$, $a(1) = 2$, $a(2) = 2$, $a(3) = 4$, $a(4) = 5$, $a(5) = 6$, $a(6) = 8$,
$a(7) = 9$, and $a(8) = 10$. See [Be06, Section 5], [Su26a], and [Su26b, Theorem 3.3].
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/cubic-acute-sets/CubicAcuteSets/ExactBounds.lean#L4147"]
theorem a_8 : a 8 = 10 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Lower-bound record in dimension $n = 16$: $a(16) \ge 129$, improving on $2^{15 - 8} = 128$.
See [Su26a] and [Su26b, Table 1].
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/cubic-acute-sets/CubicAcuteSets/Records.lean#L41"]
theorem a_16_ge : 129 ≤ a 16 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Lower-bound record in dimension $n = 26$: $a(26) \ge 250$.
See [Su26b, Table 1].
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/mariyaholic/lean-fc-proofs/blob/40a4fb03d8a97357a12f656c7347cdfc82db5754/lean/cubic-acute-sets/CubicAcuteSets/RecordsII.lean#L300"]
theorem a_26_ge : 250 ≤ a 26 := by
  sorry

/-- What is the maximum cardinality $a(11)$ of an acute set in $\{0, 1\}^{11}$?
Known bounds satisfy $24 \le a(11) \le 1024$; see [Be06], [Ha11], and [A089676](https://oeis.org/A089676). -/
def a_11_value.answer : ℕ := sorry

/--
What is the exact value of $a(11)$, the first term not listed in the official OEIS b-file
`b089676.txt` ($0 \le n \le 10$)?
-/
@[category research open, question value, AMS 5 52]
theorem a_11_value : a 11 = a_11_value.answer := by
  sorry

end OeisA89676

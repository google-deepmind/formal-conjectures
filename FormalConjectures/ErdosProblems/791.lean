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
# Erdős Problem 791

*References:*
- [erdosproblems.com/791](https://www.erdosproblems.com/791)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_.
  A Survey of Combinatorial Theory (1973), 117–138.
- [Mr79] Mrose, A., _Untere Schranken für die Reichweiten von Extremalbasen
  fester Ordnung_. Abh. Math. Sem. Univ. Hamburg 48 (1979), 118–124.
- [Ko17] Kohonen, J., _An improved lower bound for finite additive 2-bases_.
  J. Number Theory 174 (2017), 518–524. [arXiv](https://arxiv.org/abs/1606.04770).
- [Lean proof](https://github.com/AItoBit/formal-conjectures/blob/ad02f3317d9feb1283d8d9168e91aa3340ff2211/Main791.lean)
-/

@[expose] public section

namespace Erdos791


/-- A finite additive 2-basis for the interval from zero through n.
The two summands may be equal. -/
def IsBasis (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 0 n ∧
    ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m

/-- Every interval has a finite additive 2-basis. -/
@[category API, AMS 5 11]
theorem exists_basis_card (n : ℕ) :
    ∃ k : ℕ, ∃ A : Finset ℕ, IsBasis n A ∧ A.card = k := by
  refine ⟨(Finset.Icc 0 n).card, Finset.Icc 0 n, ⟨fun _ h => h, ?_⟩, rfl⟩
  intro m hm
  exact ⟨m, by simp [hm], 0, by simp, by omega⟩

/-- Minimum cardinality of a basis, counting the necessary zero element. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_basis_card n)

/-- Let $g(n)$ be minimal such that there exists $A\subseteq \{0,\ldots,n\}$ of size
$g(n)$ with $\{0,\ldots,n\}\subseteq A+A$. Estimate $g(n)$. In particular is it true
that $g(n)\sim 2n^{1/2}$?

The disproof of $g(n)\sim 2n^{1/2}$ was accomplished by Mrose [Mr79].
The linked proof uses the seven-segment construction in [Ko17, Example 2].
This statement records the negative answer to the second question. The sharp
asymptotic estimate remains open.
-/
@[category research solved, question, AMS 5 11, formal_proof using lean4 at "https://github.com/AItoBit/formal-conjectures/blob/ad02f3317d9feb1283d8d9168e91aa3340ff2211/Main791.lean"]
theorem erdos_791.parts.ii :
    ¬ Filter.Tendsto (fun n : ℕ ↦ (g n : ℝ) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds 2) := by sorry

/-- The seven-segment construction in [Ko17, Example 2] gives
$g(14t^2-1)\leq 7(t+1)$ for every integer $t\geq2$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/AItoBit/formal-conjectures/blob/ad02f3317d9feb1283d8d9168e91aa3340ff2211/Main791.lean"]
theorem erdos_791.variants.seven_segment_bound (t : ℕ) (ht : 2 ≤ t) :
    g (14 * t ^ 2 - 1) ≤ 7 * (t + 1) := by sorry

end Erdos791


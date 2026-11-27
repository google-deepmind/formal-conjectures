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
# Erdős Problem 643

*References:*
- [erdosproblems.com/643](https://www.erdosproblems.com/643)
- [Fu84] F\"uredi, Z., Hypergraphs in which all disjoint pairs have distinct unions. Combinatorica
  (1984), 161--168.
- [PiVe09] Pikhurko, Oleg and Verstra\"{e}te, Jacques, The maximum size of hypergraphs without
  generalized 4-cycles. J. Combin. Theory Ser. A (2009), 637--649.
- [HMY26] Huang, Hao, Ma, Jie, and Yang, Tianchi, *Extremal hypergraphs without generalized
  4-cycles*. [arXiv:2609.37744](https://arxiv.org/abs/2609.37744) (2026), Theorem 1.2.
- [YL26] Liu, Yilin, *Extremal Uniform Hypergraphs with Distinct Unions of Disjoint Edges*
  (2026), Theorem 1.
  [Manuscript](https://github.com/icekylinx/jsp-000523-proof/blob/264a53c8375af72b34a14d808593b07a9830287e/paper/proof.pdf)
  and [Lean formalization](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000012&version=1).
- [Zh26] Zhang, Leilei, *Extremal 3-uniform hypergraphs without generalized 4-cycles*.
  [arXiv:2610.34038](https://arxiv.org/abs/2610.34038) (2026), Theorem 1.4.
-/

@[expose] public section

namespace Erdos643

open Filter Asymptotics

/-- The least number of edges forcing two distinct disjoint pairs with the same union.
It is one more than the maximum size of an avoiding family. -/
noncomputable def forcingThreshold (n t : ℕ) : ℕ :=
  Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) + 1

def erdos_643.parts.i.answer : ℕ → ℕ → ℝ := sorry

/--
Let $f(n;t)$ be minimal such that if a $t$-uniform hypergraph on $n$ vertices contains at least
$f(n;t)$ edges then there must be four edges $A,B,C,D$ such that
$$A\cup B= C\cup D$$
and
$$A\cap B=C\cap D=\emptyset.$$
Estimate $f(n;t)$ - in particular, is it true that for $t\geq 3$
$$f(n;t)=(1+o(1))\binom{n}{t-1}?$$
-/
@[category research open, question value, AMS 5]
theorem erdos_643.parts.i :
    ∀ t : ℕ, 1 ≤ t →
      (fun n ↦ (forcingThreshold n t : ℝ)) ~[atTop] erdos_643.parts.i.answer t := by
  sorry

/--
Is it true that $f(n;t)=(1+o(1))\binom{n}{t-1}$ for $t\geq 3$?

Liu [YL26, Theorem 1] gives an affirmative answer for every fixed $t\geq 3$
and formalizes it in Lean. For rank three, Liu [YL26, Theorem 1] and Zhang [Zh26, Theorem 1.4]
give the upper bound $\binom{n}{2}$ for the size of an avoiding family.
For $t\geq 4$, see the exact extremal formula below.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000012&version=1"]
theorem erdos_643.parts.ii :
    ∀ t : ℕ, 3 ≤ t →
    (fun n ↦ (forcingThreshold n t : ℝ)) ~[atTop]
        (fun n ↦ (n.choose (t - 1) : ℝ)) := by
  sorry

/-- Liu [YL26, Theorem 1] and Huang, Ma, and Yang [HMY26, Theorem 1.2] determine the maximum
size of an avoiding family for each fixed $t\geq 4$ and all sufficiently large $n$:
$$\binom{n-1}{t-1}+\left\lfloor\frac{n-1}{t}\right\rfloor.$$
The forcing threshold is one larger. The linked Lean proof is Liu's. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000012&version=1"]
theorem erdos_643.variants.exact_t_ge_four :
    ∀ t : ℕ, 4 ≤ t → ∀ᶠ n : ℕ in atTop,
      Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) =
        (n - 1).choose (t - 1) + (n - 1) / t := by
  sorry

/-- The largest avoiding family attains the value one below the forcing threshold. -/
@[category API, AMS 5]
theorem exists_avoiding_maximizer (n t : ℕ) :
    ∃ H : Finset (Finset (Fin n)), H.IsUniform t ∧ ¬ H.HasRepeatedDisjointUnion ∧
      H.card + 1 = forcingThreshold n t := by
  classical
  let S := ((Finset.univ : Finset (Fin n)).powersetCard t).powerset.filter
    fun H ↦ ¬ H.HasRepeatedDisjointUnion
  have hne : S.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [S, Finset.HasRepeatedDisjointUnion]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  have hmem := Finset.mem_filter.1 hH
  refine ⟨H, ?_, hmem.2, ?_⟩
  · intro e he
    exact (Finset.mem_powersetCard.1 (Finset.mem_powerset.1 hmem.1 he)).2
  · unfold forcingThreshold
    apply congrArg (fun k : ℕ ↦ k + 1)
    calc
      H.card = S.sup Finset.card := hmax.symm
      _ = Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) := by
        unfold Hypergraph.extremalNumber
        congr 1
        ext K
        simp [S]

/-- A bound is at least the forcing threshold exactly when every uniform family with that
many edges contains the forbidden four-edge configuration. -/
@[category API, AMS 5]
theorem forcingThreshold_le_iff (n t m : ℕ) :
    forcingThreshold n t ≤ m ↔
      ∀ H : Finset (Finset (Fin n)), H.IsUniform t →
        m ≤ H.card → H.HasRepeatedDisjointUnion := by
  classical
  constructor
  · intro hm H hHt hcard
    by_contra hfree
    have hmem : H ∈ ((Finset.univ : Finset (Fin n)).powersetCard t).powerset.filter
        (fun H ↦ ¬ H.HasRepeatedDisjointUnion) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, hfree⟩
      intro e he
      exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hHt e he⟩
    have hmax : H.card < forcingThreshold n t := by
      unfold forcingThreshold
      apply Nat.lt_succ_of_le
      unfold Hypergraph.extremalNumber
      apply Finset.le_sup
      simpa using hmem
    omega
  · intro hm
    obtain ⟨H, hHt, hfree, hmax⟩ := exists_avoiding_maximizer n t
    by_contra hlt
    exact hfree (hm H hHt (by omega))

/-- When no edge of size $t$ fits in the ground set, the threshold is one. -/
@[category test, AMS 5]
theorem forcingThreshold_eq_one_of_lt {n t : ℕ} (h : n < t) :
    forcingThreshold n t = 1 := by
  classical
  have hempty : (Finset.univ : Finset (Fin n)).powersetCard t = ∅ :=
    Finset.powersetCard_eq_empty.2 (by simpa using h)
  simp [forcingThreshold, Hypergraph.extremalNumber, hempty, Finset.HasRepeatedDisjointUnion]

end Erdos643

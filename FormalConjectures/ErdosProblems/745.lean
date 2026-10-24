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
# Erdős Problem 745: Second-largest component of a random graph

*Reference:* [erdosproblems.com/745](https://www.erdosproblems.com/745)

At the stated parameter $p=1/n$, the second-largest component has order
$n^{2/3}$ in probability. The logarithmic bound applies to fixed
$p=\lambda/n$ with $\lambda>1$.

[Al97] Aldous, D., Brownian excursions, critical random graphs and the multiplicative
coalescent. Ann. Probab. 25 (1997), 812–854.

[KSS80] Komlós, J., Sulyok, M. and Szemerédi, E., Second largest component in a random
graph. Studia Sci. Math. Hungar. 15 (1980), 391–395.
-/

@[expose] public section

open MeasureTheory
open scoped Topology unitInterval

namespace Erdos745

/-- The edge probability $1/n$, with zero at the empty index. -/
noncomputable def criticalEdgeProbability (n : ℕ) : unitInterval :=
  if hn : n = 0 then 0 else
    ⟨(1 : ℝ) / n, unitInterval.div_mem (by positivity) (Nat.cast_nonneg n)
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))⟩

/-- The independent-edge random graph $G(n,1/n)$. -/
noncomputable def criticalRandomGraph (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (criticalEdgeProbability n)

/-- The multiset of component sizes, retaining repetitions. -/
noncomputable def componentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Multiset ℕ := by
  classical
  exact (Finset.univ : Finset G.ConnectedComponent).val.map fun C ↦ C.supp.ncard

/-- Component sizes listed in decreasing order. -/
noncomputable def rankedComponentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : List ℕ :=
  (componentOrders G).sort (· ≥ ·)

/-- The second-largest component size, or zero if fewer than two components exist. -/
noncomputable def secondLargestComponentOrder {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (rankedComponentOrders G).getD 1 0

/-- The probability of an event in $G(n,1/n)$. -/
noncomputable def criticalProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (criticalRandomGraph n).real {G | P G}

/-- The edge probability $\lambda/n$, clipped to $[0,1]$ at small indices. -/
noncomputable def edgeProbability (lam : ℝ) (n : ℕ) : unitInterval :=
  ⟨max 0 (min 1 (lam / n)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

/-- The independent-edge random graph with clipped edge probability $\lambda/n$. -/
noncomputable def randomGraph (lam : ℝ) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (edgeProbability lam n)

/-- The probability of an event in the model with parameter $\lambda$. -/
noncomputable def probability (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (randomGraph lam n).real {G | P G}

/-- In $G(n,1/n)$ the second-largest component has order $n^{2/3}$ in probability.
The two positive constants may depend on the probability tolerance. -/
@[category research solved, AMS 5 60,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos745.lean"]
theorem erdos_745 :
    ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 - ε ≤ criticalProbability n (fun G ↦
          c * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (secondLargestComponentOrder G : ℝ) ∧
          (secondLargestComponentOrder G : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) := by
  sorry

/-- For fixed $\lambda>1$, every constant above
$(\lambda-1-\log\lambda)^{-1}$ gives a logarithmic upper bound with high probability. -/
@[category research solved, AMS 5 60,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos745.lean"]
theorem erdos_745.variants.supercritical (lam : ℝ) (hlam : 1 < lam) (A : ℝ)
    (hA : 1 / (lam - 1 - Real.log lam) < A) :
    Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1) := by
  sorry

/-- For each fixed $\lambda>0$ with $\lambda\ne1$, the second-largest component size,
divided by $\log n$, converges in probability to $(\lambda-1-\log\lambda)^{-1}$. -/
@[category research solved, AMS 5 60,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos745.lean"]
theorem erdos_745.variants.noncritical_asymptotic
    (lam : ℝ) (hlam : 0 < lam) (hne : lam ≠ 1) :
    ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      |(secondLargestComponentOrder G : ℝ) / Real.log (n : ℝ) -
        1 / (lam - 1 - Real.log lam)| < ε)) Filter.atTop (𝓝 1) := by
  sorry

end Erdos745

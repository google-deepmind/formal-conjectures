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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 746

*Reference:* [erdosproblems.com/746](https://www.erdosproblems.com/746)

A conjecture of Erdős and Rényi [ErRe66]. Pósa [Po76] showed this with $Cn \log n$ edges
for some large $C$, Korshunov [Ko77] improved the threshold, and Komlós and Szemerédi [KoSz83]
proved the sharp result that with $(1/2)n \log n + (1/2)n \log \log n + cn$ edges the probability
of being Hamiltonian tends to $e^{-e^{-2c}}$.
-/

open SimpleGraph Finset

namespace Erdos746

/-- The simple graph on $\operatorname{Fin} n$ determined by a Boolean edge configuration. -/
def toGraph {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := fun v ⟨h, _⟩ => h rfl

/-- The number of edges in a Boolean edge configuration on $\operatorname{Fin} n$
(counting only pairs $i < j$ to avoid double-counting). -/
def edgeCount {n : ℕ} (ec : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ ec p.1 p.2 = true)).card

/-- The set of all edge configurations on $\operatorname{Fin} n$ with exactly $m$ edges. -/
def graphsWithEdges (n m : ℕ) : Finset (Fin n → Fin n → Bool) :=
  Finset.univ.filter (fun ec => edgeCount ec = m)

open Classical in
/-- The fraction of graphs on $\operatorname{Fin} n$ with exactly $m$ edges that satisfy
property $P$ (the $G(n,m)$ probability of $P$). Returns $0$ if there are
no graphs with exactly $m$ edges. -/
noncomputable def gnmFraction (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((graphsWithEdges n m).filter (fun ec => P (toGraph ec))).card /
  ((graphsWithEdges n m).card : ℝ)

/--
Erdős Problem 746 [ErRe66, KoSz83]:

For every $\varepsilon > 0$, almost surely a random graph on $n$ vertices with at least
$(1/2 + \varepsilon) \cdot n \cdot \log n$ edges is Hamiltonian.

Formally: for every $\varepsilon > 0$ and $\delta > 0$, there exists $n_0$ such that for all
$n \geq n_0$ and all $m$ with $(1/2 + \varepsilon) \cdot n \cdot \log n \leq m \leq \binom{n}{2}$,
the $G(n,m)$-probability that the graph is Hamiltonian is at least $1 - \delta$.

Proved by Komlós and Szemerédi [KoSz83].
-/
@[category research solved, AMS 5 60]
theorem erdos_746 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ m : ℕ, (m : ℝ) ≥ (1/2 + ε) * (n : ℝ) * Real.log (n : ℝ) →
        m ≤ n.choose 2 →
        gnmFraction n m (fun G => G.IsHamiltonian) ≥ 1 - δ := by
  sorry

end Erdos746

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
# Erdős Problem 1024

*Reference:* [erdosproblems.com/1024](https://www.erdosproblems.com/1024)

Let $f(n)$ be such that every $3$-uniform linear hypergraph on $n$ vertices contains
an independent set on $f(n)$ vertices.

A hypergraph is linear if $|A \cap B| \leq 1$ for all edges $A$ and $B$. An independent
set of vertices is one which contains no edges. A $3$-uniform linear hypergraph
is sometimes called a partial Steiner triple system.

Erdős proved $n^{1/2} \ll f(n) \ll n^{2/3}$. Phelps and Rödl [PhRo86] proved
$f(n) \asymp (n \log n)^{1/2}$.

[PhRo86] Phelps, K. T. and Rödl, V., _Steiner triple systems with minimum independence
number_. Ars Combin. 21 (1986), 167–172.
-/

open Finset

namespace Erdos1024

/-- A $3$-uniform hypergraph on `Fin n`: a family of $3$-element subsets. -/
structure Hypergraph3Uniform (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A $3$-uniform hypergraph is *linear* if any two distinct edges share
    at most one vertex. -/
def Hypergraph3Uniform.IsLinear {n : ℕ} (H : Hypergraph3Uniform n) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- A set $S$ of vertices is *independent* in $H$ if no edge of $H$ is
    contained in $S$. -/
def Hypergraph3Uniform.IsIndependent {n : ℕ} (H : Hypergraph3Uniform n)
    (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ H.edges, ¬(e ⊆ S)

/-- The independence number of $H$: the maximum size of an independent set. -/
noncomputable def Hypergraph3Uniform.independenceNumber {n : ℕ}
    (H : Hypergraph3Uniform n) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n), H.IsIndependent S ∧ S.card = k}

/-- `linearHypergraphIndNum n` is the minimum independence number over all
    $3$-uniform linear hypergraphs on $n$ vertices, i.e. the largest $f$ such
    that every such hypergraph has an independent set of size at least $f$. -/
noncomputable def linearHypergraphIndNum (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ H : Hypergraph3Uniform n, H.IsLinear ∧
    H.independenceNumber = k}

/--
Erdős Problem 1024 (solved by Phelps–Rödl [PhRo86]):

$f(n) \asymp (n \log n)^{1/2}$, where $f(n)$ is the minimum independence number over
all $3$-uniform linear hypergraphs on $n$ vertices.

There exist constants $C_1, C_2 > 0$ and $N_0$ such that for all $n \geq N_0$,
$$C_1 \sqrt{n \log n} \leq f(n) \leq C_2 \sqrt{n \log n}.$$
-/
@[category research solved, AMS 5]
theorem erdos_1024 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * Real.sqrt (↑n * Real.log ↑n) ≤ ↑(linearHypergraphIndNum n) ∧
      ↑(linearHypergraphIndNum n) ≤ C₂ * Real.sqrt (↑n * Real.log ↑n) := by
  sorry

end Erdos1024

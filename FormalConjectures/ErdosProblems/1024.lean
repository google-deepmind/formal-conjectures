/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1024

*References:*
- [erdosproblems.com/1024](https://www.erdosproblems.com/1024)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [PhRo86] Phelps, K. T. and Rödl, V., *Steiner triple systems with minimum independence number*.
  Ars Combin. (1986), 167-172.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1024

/-- A hypergraph is *linear* if any two distinct edges meet in at most one vertex. -/
def IsLinear {V : Type*} [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1

/-- The independence number of a hypergraph: the largest size of a set of vertices containing
no edge. -/
noncomputable def indepNum {V : Type*} (H : Finset (Finset V)) : ℕ :=
  sSup {k | ∃ I : Finset V, I.card = k ∧ ∀ e ∈ H, ¬ e ⊆ I}

/--
`f n` is the largest integer such that every $3$-uniform linear hypergraph on `n` vertices
contains an independent set on `f n` vertices, i.e. the minimum of the independence number over
all such hypergraphs.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Finset (Finset (Fin n)), H.IsThreeUniform ∧ IsLinear H ∧ indepNum H = k}

/--
Let $f(n)$ be such that every $3$-uniform linear hypergraph on $n$ vertices contains an
independent set on $f(n)$ vertices. Estimate $f(n)$.

A hypergraph is linear if $\lvert A\cap B\rvert\leq 1$ for all edges $A$ and $B$. An independent
set of vertices is one which contains no edges. A $3$-uniform linear hypergraph is sometimes
called a partial Steiner triple system.

Erdős could prove $n^{1/2} \ll f(n) \ll n^{2/3}$. Phelps and Rödl [PhRo86] proved
$$f(n) \asymp (n\log n)^{1/2}.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1024.lean#L338"]
theorem erdos_1024 : (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] fun n ↦ √(n * Real.log n) := by
  sorry

/-- Erdős could prove $n^{1/2} \ll f(n) \ll n^{2/3}$. -/
@[category research solved, AMS 5]
theorem erdos_1024.variants.erdos_bounds :
    (fun n : ℕ ↦ √(n : ℝ)) =O[atTop] (fun n ↦ (f n : ℝ)) ∧
      (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (2 / 3 : ℝ) := by
  sorry

end Erdos1024

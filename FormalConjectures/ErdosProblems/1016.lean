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
# Erdős Problem 1016

*Reference:* [erdosproblems.com/1016](https://www.erdosproblems.com/1016)

Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n + h(n)$
edges which contains a cycle on $k$ vertices, for all $3 \leq k \leq n$. Such graphs
are called pancyclic. Estimate $h(n)$. In particular, is it true that
$$h(n) \geq \log_2 n + \log^* n - O(1),$$
where $\log^* n$ is the iterated logarithmic function?

A problem of Bondy [Bo71], who claimed a proof (without details) of
$$\log_2(n-1) - 1 \leq h(n) \leq \log_2 n + \log^* n + O(1).$$
Erdős [Er71] believed the upper bound is closer to the truth. Griffin [Gr13] gave
the first proof of the lower bound. George, Khodkar, and Wallis [GKW16] gave the
first published proof of the upper bound.

OEIS: [A105206](https://oeis.org/A105206)

[Bo71] Bondy, J.A., _Pancyclic graphs. I_. J. Combinatorial Theory Ser. B (1971), 80–84.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.

[Gr13] Griffin, S., _Minimal Pancyclicity_. arXiv:1312.0274 (2013).

[GKW16] George, J.C., Khodkar, A., Wallis, W.D., _Pancyclic and bipancyclic graphs_.
(2016), xii+108.
-/

open Finset Classical

namespace Erdos1016

/-- A simple graph on `Fin n` contains a simple cycle of length $k$ (for $k \geq 3$)
    if there is an injective map from `Fin k` into the vertices such that
    consecutive vertices in the cycle map to adjacent vertices.
    The injectivity requirement ensures this is a simple cycle. -/
def ContainsCycle {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (hk : k ≥ 3) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    ∀ i : Fin k, G.Adj (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)

/-- A graph on `Fin n` is pancyclic if it contains cycles of every length
    from $3$ to $n$. -/
def IsPancyclic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k (hk : k ≥ 3), k ≤ n → ContainsCycle G k hk

/-- The minimum excess edges $h(n)$ for a pancyclic graph: the smallest $h$ such
    that there exists a pancyclic graph on $n$ vertices with $n + h$ edges.
    Note: for $n < 3$, no graph is pancyclic, so the set is empty and
    `sInf ∅ = 0` in `ℕ`. The theorems below restrict to $n \geq 3$. -/
noncomputable def pancyclicExcess (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∃ G : SimpleGraph (Fin n),
    G.edgeFinset.card = n + h ∧ IsPancyclic G}

/-- Auxiliary definition for the iterated logarithm with explicit fuel.
    The fuel parameter is needed for structural recursion in Lean, even though
    `Nat.log 2` strictly decreases on inputs `≥ 2`. Using `n` as fuel suffices
    since `Nat.log 2 n < n` for all `n ≥ 2`. -/
def iteratedLog₂Aux : ℕ → ℕ → ℕ
  | _, 0 => 0
  | _, 1 => 0
  | 0, _ + 2 => 0
  | fuel + 1, n + 2 => 1 + iteratedLog₂Aux fuel (Nat.log 2 (n + 2))

/-- The iterated logarithm $\log^*(n)$ (base $2$). -/
def iteratedLog₂ (n : ℕ) : ℕ := iteratedLog₂Aux n n

/--
Erdős Problem 1016 [Er71]:

The minimum number of edges beyond $n$ needed for a pancyclic graph on $n$
vertices satisfies $h(n) \geq \lfloor\log_2 n\rfloor + \log^* n - O(1)$.

Formulated as: there exists a constant $C$ such that for all $n \geq 3$,
$h(n) + C \geq \lfloor\log_2 n\rfloor + \log^* n$.
-/
@[category research open, AMS 5]
theorem erdos_1016 : answer(sorry) ↔
    ∃ C : ℕ, ∀ n, n ≥ 3 →
      pancyclicExcess n + C ≥ Nat.log 2 n + iteratedLog₂ n := by
  sorry

/--
Erdős Problem 1016 — upper bound [Bo71] [GKW16]:

Bondy claimed, and George–Khodkar–Wallis proved, that
$h(n) \leq \lfloor\log_2 n\rfloor + \log^* n + O(1)$.

Formulated as: there exists a constant $C$ such that for all $n \geq 3$,
$\lfloor\log_2 n\rfloor + \text{iteratedLog}_2(n) \leq \text{pancyclicExcess}(n) + C$
is *not* needed — rather, the excess itself is at most
$\lfloor\log_2 n\rfloor + \log^* n + C$.
-/
@[category research solved, AMS 5]
theorem erdos_1016_upper :
    ∃ C : ℕ, ∀ n, n ≥ 3 →
      pancyclicExcess n ≤ Nat.log 2 n + iteratedLog₂ n + C := by
  sorry

/--
Erdős Problem 1016 — Griffin's lower bound [Gr13]:

Griffin proved $h(n) \geq \lfloor\log_2(n-1)\rfloor - 1$ for all $n \geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_1016_lower :
    ∀ n, n ≥ 3 →
      pancyclicExcess n + 1 ≥ Nat.log 2 (n - 1) := by
  sorry

end Erdos1016

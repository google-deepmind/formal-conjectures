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
# Erdős Problem 1216

*References:*
- [erdosproblems.com/1216](https://www.erdosproblems.com/1216)
- [ErMo64] Erdős, P. and Moser, L., *On the representation of directed graphs as unions of
  orderings*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1964), 125-132.
- [St59] Stearns, Richard, *The voting problem*. Amer. Math. Monthly (1959), 761-763.
- [RePa70] Reid, K. B. and Parker, E. T., *Disproof of a conjecture of Erdős and Moser on
  tournaments*. J. Combinatorial Theory (1970), 225-238.
- [Sa94] Sánchez-Flores, Adolfo, *On tournaments and their largest transitive subtournaments*.
  Graphs Combin. (1994), 367-376.
- [Sa98b] Sanchez-Flores, Adolfo, *On tournaments free of large transitive subtournaments*. Graphs
  Combin. (1998), 181-200.
-/

@[expose] public section

namespace Erdos1216

/--
A tournament `G` contains a transitive tournament on `k` vertices: `k` distinct vertices
`v 0, …, v (k-1)` with `v i → v j` whenever `i < j`.
-/
def HasTransitiveSubtournament {V : Type*} (G : Digraph V) (k : ℕ) : Prop :=
  ∃ v : Fin k → V, Function.Injective v ∧ ∀ i j : Fin k, i < j → G.Adj (v i) (v j)

/--
`f n` is the largest `k` such that every tournament on `n` vertices contains a transitive
tournament on `k` vertices.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k | ∀ G : Digraph (Fin n), G.IsTournament → HasTransitiveSubtournament G k}

/--
A tournament is a complete directed graph. Let $f(n)$ be such that every tournament on $n$
vertices contains a transitive tournament on $f(n)$ vertices (i.e. one such that if
$i\to j\to k$ then $i\to k$).

Is it true that $f(n)=\lfloor \log_2 n\rfloor +1$?

The inverse of the function $f(n)$ is sometimes known as the directed Ramsey number.

Stearns [St59] proved that $f(n)\geq \lfloor \log_2 n\rfloor+1$ (the proof is a greedy
construction, using the observation that any tournament must contain a vertex with out-degree at
least $\frac{n-1}{2}$). Erdős and Moser [ErMo64] proved that
$f(n) \leq 2\lfloor \log_2 n\rfloor+1$, and note that $f(7)=3$.

Reid and Parker [RePa70] answered this question in the negative for all $n\geq 14$, proving that
$f(n) \geq \lfloor \log_2n + 4-\log_27\rfloor$ for all $n\geq 14$. This was improved for
$n\geq 55$ by Sanchez-Flores [Sa94] to $f(n) \geq \lfloor \log_2 n-\log_2(55)\rfloor+7$, and
further for $n\geq 32$ to $f(n) \geq \lfloor \log_2 n-\log_2(54)\rfloor+7$ by Sanchez-Flores
[Sa98b]. (Note that $7-\log_2(54)\approx 1.24$.)
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1216.lean#L1178"]
theorem erdos_1216 : answer(False) ↔ ∀ n : ℕ, 1 ≤ n → f n = Nat.log 2 n + 1 := by
  sorry

/-- The first counterexample: $f(14) = 5$, whereas $\lfloor \log_2 14\rfloor + 1 = 4$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1216.lean#L1167"]
theorem erdos_1216.variants.fourteen : f 14 = 5 := by
  sorry

/-- Stearns [St59] proved that $f(n)\geq \lfloor \log_2 n\rfloor+1$. -/
@[category research solved, AMS 5]
theorem erdos_1216.variants.stearns : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + 1 ≤ f n := by
  sorry

/-- Erdős and Moser [ErMo64] proved that $f(n) \leq 2\lfloor \log_2 n\rfloor+1$. -/
@[category research solved, AMS 5]
theorem erdos_1216.variants.erdos_moser : ∀ n : ℕ, 1 ≤ n → f n ≤ 2 * Nat.log 2 n + 1 := by
  sorry

/-- Erdős and Moser [ErMo64] note that $f(7)=3$. -/
@[category research solved, AMS 5]
theorem erdos_1216.variants.seven : f 7 = 3 := by
  sorry

/--
Reid and Parker [RePa70] proved that $f(n) \geq \lfloor \log_2n + 4-\log_27\rfloor$ for all
$n\geq 14$.
-/
@[category research solved, AMS 5]
theorem erdos_1216.variants.reid_parker : ∀ n : ℕ, 14 ≤ n →
    ⌊Real.logb 2 n + 4 - Real.logb 2 7⌋ ≤ f n := by
  sorry

/--
Sanchez-Flores [Sa98b] proved that $f(n) \geq \lfloor \log_2 n-\log_2(54)\rfloor+7$ for all
$n\geq 32$.
-/
@[category research solved, AMS 5]
theorem erdos_1216.variants.sanchez_flores : ∀ n : ℕ, 32 ≤ n →
    ⌊Real.logb 2 n - Real.logb 2 54⌋ + 7 ≤ f n := by
  sorry

end Erdos1216

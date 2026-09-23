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
# Erdős Problem 804

*References:*
- [erdosproblems.com/804](https://www.erdosproblems.com/804)
- [Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number
  theory_. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [AlSu07] Alon, Noga and Sudakov, Benny, _On graphs with subgraphs having large independence
  numbers_. J. Graph Theory (2007), 149-157.
-/

@[expose] public section

open Filter Real

namespace Erdos804

/-- A graph `G` on `n` vertices in which every induced subgraph on `m` vertices has an
independent set of size at least `t`. -/
def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n)) (m t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m → ∃ I ⊆ S, t ≤ I.card ∧ G.IsIndepSet I

/-- `f m n` is maximal such that any graph on `n` vertices in which every induced subgraph on `m`
vertices has an independent set of size at least $\log n$ must contain an independent set of size
at least `f m n`. -/
noncomputable def f (m n : ℕ) : ℕ :=
  sInf {k | ∃ G : SimpleGraph (Fin n), HasLocalIndependence G m ⌈log n⌉₊ ∧ G.indepNum = k}

/--
Let $f(m,n)$ be maximal such that any graph on $n$ vertices in which every induced subgraph on
$m$ vertices has an independent set of size at least $\log n$ must contain an independent set of
size at least $f(n)$.

Estimate $f(n)$. In particular, is it true that $f((\log n)^2,n) \geq n^{1/2-o(1)}$?

The answer is no: Alon and Sudakov [AlSu07] proved that in fact
$$\frac{(\log n)^2}{\log\log n}\ll f((\log n)^2,n) \ll (\log n)^2.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos804.lean#L3532"]
theorem erdos_804.parts.i : answer(False) ↔
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 2 - ε : ℝ) ≤ f ⌊(log n) ^ 2⌋₊ n := by
  sorry

/--
Is it true that $f((\log n)^3,n)\gg (\log n)^3$?

The answer is no: Alon and Sudakov [AlSu07] proved that in fact
$$f((\log n)^3,n)\asymp \frac{(\log n)^2}{\log\log n}.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos804.lean#L3532"]
theorem erdos_804.parts.ii : answer(False) ↔
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * (log n) ^ 3 ≤ f ⌊(log n) ^ 3⌋₊ n := by
  sorry

/--
Alon and Sudakov [AlSu07] proved that
$$\frac{(\log n)^2}{\log\log n}\ll f((\log n)^2,n) \ll (\log n)^2$$
and
$$f((\log n)^3,n)\asymp \frac{(\log n)^2}{\log\log n}.$$
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos804.lean#L3532"]
theorem erdos_804.variants.alon_sudakov :
    ∃ c₂ C₂ c₃ C₃ : ℝ, 0 < c₂ ∧ 0 < C₂ ∧ 0 < c₃ ∧ 0 < C₃ ∧
    ∀ᶠ n : ℕ in atTop,
      c₂ * ((log n) ^ 2 / log (log n)) ≤ f ⌊(log n) ^ 2⌋₊ n ∧
      (f ⌊(log n) ^ 2⌋₊ n : ℝ) ≤ C₂ * (log n) ^ 2 ∧
      c₃ * ((log n) ^ 2 / log (log n)) ≤ f ⌊(log n) ^ 3⌋₊ n ∧
      (f ⌊(log n) ^ 3⌋₊ n : ℝ) ≤ C₃ * ((log n) ^ 2 / log (log n)) := by
  sorry

end Erdos804

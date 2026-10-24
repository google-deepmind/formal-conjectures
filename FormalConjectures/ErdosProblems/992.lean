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
# Erdős Problem 992

*References:*
- [erdosproblems.com/992](https://www.erdosproblems.com/992)
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math.
  (1964), 52-65.
- [ErKo49] Erdős, P. and Koksma, J. F., *On the uniform distribution modulo $1$ of sequences
  $(f(n,\theta))$*. Nederl. Akad. Wetensch., Proc. (1949), 851--854 = Indagationes Math. 11,
  299--302.
- [Ca50] Cassels, J. W. S., *Some metrical theorems of Diophantine approximation. III*. Proc.
  Cambridge Philos. Soc. (1950), 219--225.
- [Ba81] Baker, R. C., *Metric number theory and the large sieve*. J. London Math. Soc. (2)
  (1981), 34--40.
- [BePh94] Berkes, István and Philipp, Walter, *The size of trigonometric and Walsh series and
  uniform distribution mod $1$*. J. London Math. Soc. (2) (1994), 454--464.
-/

@[expose] public section

open Filter Asymptotics MeasureTheory

namespace Erdos992

/-- The discrepancy of the first $N$ fractional parts $\{\alpha x_n\}$: the supremum over
subintervals $I = [a, b) \subseteq [0,1]$ of $\lvert \#\{ n < N : \{ \alpha x_n\}\in I\} -
\lvert I\rvert N\rvert$. -/
noncomputable def discrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup {t | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
    t = |({n ∈ Finset.range N | Int.fract (α * x n) ∈ Set.Ico a b}.card : ℝ) - (b - a) * N|}

/--
Let $x_1<x_2<\cdots$ be an infinite sequence of integers. Is it true that, for almost all
$\alpha \in [0,1]$, the discrepancy
$$D(N)=\max_{I\subseteq [0,1]} \lvert \#\{ n\leq N : \{ \alpha x_n\}\in I\} - \lvert I\rvert N\rvert$$
satisfies
$$D(N) \ll N^{1/2}(\log N)^{o(1)}?$$

Erdős and Koksma [ErKo49] and Cassels [Ca50] independently proved that, for any sequence $x_i$ and
almost all $\alpha$, the discrepancy satisfies $D(N)\ll N^{1/2}(\log N)^{5/2+o(1)}$. Baker [Ba81]
improved this to $D(N)\ll N^{1/2}(\log N)^{3/2+o(1)}$.

This was disproved by Berkes and Philipp [BePh94], who constructed a sequence of integers
$x_1<x_2<\cdots$ such that, for almost all $\alpha\in[0,1]$,
$$\limsup_{N\to \infty}\frac{D(N)}{(N\log N)^{1/2}}>0.$$

The bound $D(N) \ll N^{1/2}(\log N)^{o(1)}$ is formalized as $D(N) \ll_\epsilon N^{1/2}(\log N)^\epsilon$
for every $\epsilon > 0$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos992.lean#L1128"]
theorem erdos_992 : answer(False) ↔ ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => discrepancy x α N) =O[atTop] fun N : ℕ => √N * Real.log N ^ ε := by
  sorry

/--
Or even $D(N)\ll N^{1/2}(\log\log N)^{O(1)}$?

This is also false, by the construction of Berkes and Philipp [BePh94].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos992.lean#L1128"]
theorem erdos_992.variants.loglog : answer(False) ↔ ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∃ C : ℝ,
      (fun N : ℕ => discrepancy x α N) =O[atTop]
        fun N : ℕ => √N * Real.log (Real.log N) ^ C := by
  sorry

/--
Berkes and Philipp [BePh94] constructed a sequence of integers $x_1<x_2<\cdots$ such that, for
almost all $\alpha\in[0,1]$,
$$\limsup_{N\to \infty}\frac{D(N)}{(N\log N)^{1/2}}>0.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos992.lean#L1128"]
theorem erdos_992.variants.berkes_philipp : ∃ x : ℕ → ℤ, StrictMono x ∧ ∃ c : ℝ, 0 < c ∧
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∃ᶠ N : ℕ in atTop, c * √(N * Real.log N) ≤ discrepancy x α N := by
  sorry

/--
Baker [Ba81] proved that, for any sequence $x_i$ and almost all $\alpha$, the discrepancy
satisfies $D(N)\ll N^{1/2}(\log N)^{3/2+o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_992.variants.baker : ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => discrepancy x α N) =O[atTop]
        fun N : ℕ => √N * Real.log N ^ (3 / 2 + ε) := by
  sorry

end Erdos992

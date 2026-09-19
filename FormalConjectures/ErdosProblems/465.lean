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
public import FormalConjectures.ErdosProblems.«466»

/-!
# Erdős Problem 465

*References:*
- [erdosproblems.com/465](https://www.erdosproblems.com/465)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59-79.
- [Sa76] Sárközy, A., *On distances near integers. I, II*. Studia Sci. Math. Hungar. (1976),
  37-50, 105-111.
- [Ko01] Konyagin, S. V., *On the distances between points on the plane*. Mat. Zametki (2001),
  630-633.
-/

@[expose] public section

open Filter Asymptotics Erdos466

namespace Erdos465

/--
Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen in a
circle of radius $X$ such that
$$\| \lvert P_i-P_j\rvert \| \geq \delta$$
for all $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.)

Is it true that, for any $0<\delta<1/2$, we have $N(X,\delta)=o(X)$?

The first conjecture was proved by Sárközy [Sa76], who in fact proved
$N(X,\delta) \ll \delta^{-3}\frac{X}{\log\log X}$. Konyagin [Ko01] proved the strong upper bound
$N(X,\delta) \ll_\delta X^{1/2}$.

See also [466](https://www.erdosproblems.com/466) for lower bounds and
[953](https://www.erdosproblems.com/953) for a similar problem.
-/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos465.lean#L962"]
theorem erdos_465.parts.i : answer(True) ↔ ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    (fun X : ℝ ↦ (N X δ : ℝ)) =o[atTop] fun X ↦ X := by
  sorry

/-- In fact, is it true that (for any fixed $\delta>0$) $N(X,\delta)<X^{1/2+o(1)}$? Yes, by
Konyagin's bound [Ko01]. -/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos465.lean#L962"]
theorem erdos_465.parts.ii : answer(True) ↔ ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ X : ℝ in atTop, (N X δ : ℝ) < X ^ (1 / 2 + ε) := by
  sorry

/-- Konyagin [Ko01] proved the strong upper bound $N(X,\delta) \ll_\delta X^{1/2}$. -/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos465.lean#L962"]
theorem erdos_465.variants.konyagin : ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → (N X δ : ℝ) ≤ C * √X := by
  sorry

/-- Sárközy [Sa76] proved $N(X,\delta) \ll \delta^{-3}\frac{X}{\log\log X}$. -/
@[category research solved, AMS 11 52]
theorem erdos_465.variants.sarkozy : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∀ᶠ X : ℝ in atTop, (N X δ : ℝ) ≤ C * δ⁻¹ ^ 3 * (X / Real.log (Real.log X)) := by
  sorry

end Erdos465

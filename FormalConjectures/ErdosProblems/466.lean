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
# Erdős Problem 466

*References:*
- [erdosproblems.com/466](https://www.erdosproblems.com/466)
- [Er72] Erdős, Paul, *Extremal problems in number theory*. Proceedings of the 1972 Number Theory
  Conference (Univ. Colorado, Boulder, Colo.) (1972), 80-86.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59-79.
- [Sa76] Sárközy, A., *On distances near integers. I, II*. Studia Sci. Math. Hungar. (1976), 37-50,
  105-111.
-/

@[expose] public section

open Filter Metric

namespace Erdos466

/--
`N X δ` is the maximum number of points in a closed disc of radius `X` in the plane such that
the distance between any two of them is at least `δ` away from the nearest integer.
-/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}

/--
Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen in a
circle of radius $X$ such that
$$\| \lvert P_i-P_j\rvert \| \geq \delta$$
for all $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.)

Is there some $\delta>0$ such that
$$\lim_{X\to \infty}N(X,\delta)=\infty?$$

Graham proved this is true, and in fact $N(X,1/10)> \frac{\log X}{10}$. This was substantially
improved by Sárközy [Sa76], who proved that for all sufficiently small $\delta>0$,
$N(X,\delta)>X^{1/2-\delta^{1/7}}$.
-/
@[category research solved, AMS 11 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos466.lean#L292"]
theorem erdos_466 : answer(True) ↔ ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X ↦ N X δ) atTop atTop := by
  sorry

/-- Graham proved that $N(X,1/10)> \frac{\log X}{10}$. -/
@[category research solved, AMS 11 52]
theorem erdos_466.variants.graham : ∀ X : ℝ, 1 ≤ X → Real.log X / 10 < N X (1 / 10) := by
  sorry

/--
Sárközy [Sa76] proved that for all sufficiently small $\delta>0$,
$N(X,\delta)>X^{1/2-\delta^{1/7}}$ for all sufficiently large $X$.
-/
@[category research solved, AMS 11 52]
theorem erdos_466.variants.sarkozy : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ᶠ X : ℝ in atTop, X ^ (1 / 2 - δ ^ (1 / 7 : ℝ)) < N X δ := by
  sorry

end Erdos466

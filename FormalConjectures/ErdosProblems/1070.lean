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
# Erdős Problem 1070

*References:*
- [erdosproblems.com/1070](https://www.erdosproblems.com/1070)
- [DuVa26] Dúcz, Á. and Varga, D., *A unit-distance graph in the plane with independence ratio
  below 1/4*. [arXiv:2606.28157](https://arxiv.org/abs/2606.28157) (2026).
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
  [PDF](https://www.renyi.hu/~p_erdos/1987-27.pdf)
- [MRVZ23] Matolcsi, M., Ruzsa, I. Z., Varga, D. and Zsámboki, P., *The fractional chromatic
  number of the plane is at least $4$*. [arXiv:2311.10069](https://arxiv.org/abs/2311.10069)
  (2023).

If we also insist that no two points are distance $<1$ apart, we get
[erdosproblems.com/1066](https://www.erdosproblems.com/1066).
-/

@[expose] public section

open Filter SimpleGraph
open scoped EuclideanGeometry Topology

namespace Erdos1070

/-- $f(n)$: the largest $m$ such that, for every set $X$ of $n$ distinct points of
$\mathbb{R}^2$, the graph on $X$ joining points at distance exactly $1$ has an independent set
with at least $m$ vertices. In other words, $X$ contains $m$ points, no two of which are at
distance $1$. The set of such $m$ contains $0$ and is bounded by $n$, so `sSup` is a true
maximum. For $n = 0$ the value is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ X : Finset ℝ², X.card = n →
    m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}

/-- For every finite set `X` of points, $f(|X|)$ is at most the independence number of the unit
distance graph on `X`. -/
@[category API, AMS 5 52]
theorem f_le (X : Finset ℝ²) :
    f X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum := by
  refine csSup_le ⟨0, fun _ _ => Nat.zero_le _⟩ ?_
  intro m hm
  exact hm X rfl

def erdos_1070.parts.i.answer : ℝ := sorry

/--
Let $f(n)$ be maximal such that, given any $n$ points in $\mathbb{R}^2$, there exist $f(n)$ points
such that no two are distance $1$ apart. Estimate $f(n)$. In particular, is it true that
$f(n)\geq n/4$?

This is the first part, a problem of Erdős [Er87b, p. 171]. Since $f(n)=\Theta(n)$ is already
known, we ask for $\lim f(n)/n$. The limit exists by Fekete's lemma, since placing two
configurations far apart shows $f(a+b) \leq f(a)+f(b)$.
-/
@[category research open, question value, AMS 5 52]
theorem erdos_1070.parts.i :
    Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (𝓝 erdos_1070.parts.i.answer) := by
  sorry

/--
Let $f(n)$ be maximal such that, given any $n$ points in $\mathbb{R}^2$, there exist $f(n)$ points
such that no two are distance $1$ apart. Estimate $f(n)$. In particular, is it true that
$f(n)\geq n/4$?

This is the second part, read as the inequality for every $n$. The answer is no: Dúcz and Varga
[DuVa26, Theorem 1] construct a finite unit distance graph $G$ in the plane with
$\alpha(G) < |V(G)|/4$. For its vertex set $X$, `f_le X` gives
$f(|X|) \leq \alpha(U_X) \leq \alpha(G) < |X|/4$, where $U_X$ is the unit distance graph on $X$.
-/
@[category research solved, question, AMS 5 52]
theorem erdos_1070.parts.ii : ¬ ∀ n : ℕ, (n : ℝ) / 4 ≤ (f n : ℝ) := by
  sorry

/--
The Moser spindle shows $f(n)\leq \frac{2}{7}n\approx 0.285n$.

The Moser spindle has $7$ points and independence number $2$, so $m$ far-apart copies give the
bound for $n=7m$.
-/
@[category textbook, AMS 5 52]
theorem erdos_1070.variants.moser_spindle (m : ℕ) : f (7 * m) ≤ 2 * m := by
  sorry

/--
Matolcsi, Ruzsa, Varga, and Zsámboki [MRVZ23, Section 3, after Theorem 2] showed that for every
$\varepsilon>0$ there is a finite unit distance graph $G\subseteq\mathbb{R}^2$ whose largest
independent set has size at most $(1/4+\varepsilon)|G|$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki_graphs :
    ∀ ε > (0 : ℝ), ∃ X : Finset ℝ², X.Nonempty ∧
      ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum : ℝ) ≤ (1 / 4 + ε) * X.card := by
  sorry

/--
Matolcsi, Ruzsa, Varga, and Zsámboki [MRVZ23] have improved the upper bound to
$$f(n) \leq \left(\frac{1}{4}+o(1)\right)n.$$

This follows from the previous statement by taking disjoint copies of the graph far apart.
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (1 / 4 + ε) * n := by
  sorry

end Erdos1070

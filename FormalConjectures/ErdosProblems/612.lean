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
# Erdős Problem 612

*Reference:* [erdosproblems.com/612](https://www.erdosproblems.com/612)

[EPPT89] Erdős, P., Pach, J., Pollack, R. and Tuza, Z., *Radius, diameter, and minimum
degree*. Journal of Combinatorial Theory, Series B 47 (1989).

[CSS21] Czabarka, E., Singgih, I. and Székely, L. A., *Counterexamples to a conjecture of
Erdős, Pach, Pollack and Tuza*. Journal of Combinatorial Theory, Series B 151 (2021), 38–45.

[ChCh26] Chen, H. and Chen, Y., *Counterexamples to two conjectures on the diameter of
clique-free graphs*. arXiv:2609.03346 (2026).
-/

@[expose] public section

namespace Erdos612

/--
The even-clique conjecture of [EPPT89] is false [CSS21]. It asserted that, for fixed
$r,d\geq 2$ with $(r-1)(3r+2)\mid d$, every connected $K_{2r}$-free graph on $n$
vertices with minimum degree $d$ satisfies
$D\leq \frac{2(r-1)(3r+2)}{2r^2-1}\frac nd+O(1)$.
The additive constant may depend on $r$ and $d$, but not on $n$ or the graph.
-/
@[category research solved, AMS 5]
theorem erdos_612.parts.i :
    ¬ (∀ r ≥ 2, ∀ d ≥ 2, (r - 1) * (3 * r + 2) ∣ d →
      ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), [DecidableRel G.Adj] →
        G.Connected → G.CliqueFree (2 * r) → G.minDegree = d →
          (G.diam : ℝ) ≤ (2 * ((r : ℝ) - 1) * (3 * r + 2) / (2 * r ^ 2 - 1)) *
            (n : ℝ) / d + C) := by
  sorry

/--
The odd-clique conjecture of [EPPT89] is false [ChCh26]. It asserted that, for fixed
$r,d\geq 2$ with $3r-1\mid d$, every connected $K_{2r+1}$-free graph on $n$
vertices with minimum degree $d$ satisfies
$D\leq \frac{3r-1}{r}\frac nd+O(1)$.
The additive constant may depend on $r$ and $d$, but not on $n$ or the graph.
-/
@[category research solved, AMS 5]
theorem erdos_612.parts.ii :
    ¬ (∀ r ≥ 2, ∀ d ≥ 2, 3 * r - 1 ∣ d →
      ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), [DecidableRel G.Adj] →
        G.Connected → G.CliqueFree (2 * r + 1) → G.minDegree = d →
          (G.diam : ℝ) ≤ ((3 * (r : ℝ) - 1) / r) * (n : ℝ) / d + C) := by
  sorry

/--
The amended conjecture of [CSS21] is false [ChCh26]. It asserted that, for fixed
$k\geq 3$ and $d\geq\lceil 3k/2\rceil-1$, every connected $K_{k+1}$-free graph
on $n$ vertices with minimum degree at least $d$ satisfies
$D\leq (3-2/k)n/d+O(1)$, with the constant depending only on $k$ and $d$.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.amended :
    ¬ (∀ k ≥ 3, ∀ d : ℕ, (3 * k + 1) / 2 - 1 ≤ d →
      ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), [DecidableRel G.Adj] →
        G.Connected → G.CliqueFree (k + 1) → d ≤ G.minDegree →
          (G.diam : ℝ) ≤ (3 - 2 / (k : ℝ)) * (n : ℝ) / d + C) := by
  sorry

/--
For fixed minimum degree $d\geq 2$, every connected graph on $n$ vertices satisfies
$D\leq 3n/(d+1)+O(1)$ [EPPT89].
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.general :
    ∀ d ≥ 2, ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      [DecidableRel G.Adj] → G.Connected → G.minDegree = d →
        (G.diam : ℝ) ≤ 3 * (n : ℝ) / (d + 1) + C := by
  sorry

/--
The triangle-free case of the odd-clique bound holds [EPPT89]: for fixed minimum
degree $d\geq 2$, every connected triangle-free graph satisfies $D\leq 2n/d+O(1)$.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.triangle_free :
    ∀ d ≥ 2, ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      [DecidableRel G.Adj] → G.Connected → G.CliqueFree 3 → G.minDegree = d →
        (G.diam : ℝ) ≤ 2 * (n : ℝ) / d + C := by
  sorry

/--
The $r=2$ case of the original odd-clique conjecture holds: for fixed $d\geq 2$
divisible by $5$, connected $K_5$-free graphs satisfy $D\leq 5n/(2d)+O(1)$.
This follows from Kitamura's stronger finite bound.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-612-lean/blob/66060d98c780b7c75624a3fd613fab4735803d9b/lean4web/Erdos612Lean4Web.lean"]
theorem erdos_612.variants.original_k5 :
    ∀ d ≥ 2, 5 ∣ d → ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      [DecidableRel G.Adj] → G.Connected → G.CliqueFree 5 → G.minDegree = d →
        (G.diam : ℝ) ≤ (5 / 2 : ℝ) * n / d + C := by
  sorry

/--
The $k=3$ case of the amended conjecture holds: for fixed $d\geq 4$, connected
$K_4$-free graphs with minimum degree at least $d$ satisfy $D\leq 7n/(3d)+O(1)$.
This follows from Kitamura's stronger finite bound.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-612-lean/blob/66060d98c780b7c75624a3fd613fab4735803d9b/lean4web/Erdos612Lean4Web.lean"]
theorem erdos_612.variants.amended_k3 :
    ∀ d ≥ 4, ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      [DecidableRel G.Adj] → G.Connected → G.CliqueFree 4 → d ≤ G.minDegree →
        (G.diam : ℝ) ≤ (7 / 3 : ℝ) * n / d + C := by
  sorry

/--
The $k=4$ case of the amended conjecture holds: for fixed $d\geq 5$, connected
$K_5$-free graphs with minimum degree at least $d$ satisfy $D\leq 5n/(2d)+O(1)$.
This follows from Kitamura's stronger finite bound.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-612-lean/blob/66060d98c780b7c75624a3fd613fab4735803d9b/lean4web/Erdos612Lean4Web.lean"]
theorem erdos_612.variants.amended_k4 :
    ∀ d ≥ 5, ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      [DecidableRel G.Adj] → G.Connected → G.CliqueFree 5 → d ≤ G.minDegree →
        (G.diam : ℝ) ≤ (5 / 2 : ℝ) * n / d + C := by
  sorry

end Erdos612

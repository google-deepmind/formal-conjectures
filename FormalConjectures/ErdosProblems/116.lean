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
# Erdős Problem 116

*Reference:* [erdosproblems.com/116](https://www.erdosproblems.com/116)

Erdős–Herzog–Piranian conjecture (proved): if all roots of a degree-$n$ polynomial lie in the
unit disk, the area of $\{z : |p(z)| < 1\}$ is at least $n^{-O(1)}$. Settled by Krishnapur,
Lundberg, and Ramachandran.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*, J. Analyse
Math. 6 (1958), 125–148.

[Er61] Erdős, P., *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
221–254.

[Po61] Pommerenke, Ch., *On metric properties of complex polynomials*, Michigan Math. J. 8 (1961),
97–115.

[Po28] Pólya, G., *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach
zusammenhängende Gebiete*, S.-B. Preuss. Akad. Wiss. (1928), 228–232, 280–282.

[Wa88] Wagner, G., *On the area of lemniscate domains*, J. Analyse Math. 50 (1988), 159–167.

[KLR25] Krishnapur, M., Lundberg, E., and Ramachandran, K., *On the area of polynomial
lemniscates*, arXiv:2503.18270, 2025.
-/

open scoped ENNReal

open Polynomial MeasureTheory

namespace Erdos116

/-- The lemniscate interior of a complex polynomial $p$:
    the open sublevel set $\{z \in \mathbb{C} : |p(z)| < 1\}$. -/
def lemniscateInterior (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/--
Erdős–Herzog–Piranian Conjecture (Problem #116) [EHP58, Er61]:

Let $p(z) = \prod_i (z - z_i)$ be a polynomial of degree $n \ge 1$ with all roots $z_i$
in the closed unit disk ($|z_i| \le 1$). Then the 2D Lebesgue measure (area) of
the lemniscate interior $\{z \in \mathbb{C} : |p(z)| < 1\}$ satisfies
$$
  |\{z : |p(z)| < 1\}| \gg n^{-O(1)}.
$$

That is, there exist universal constants $\kappa > 0$ and $\delta > 0$ such that for all $n \ge 1$
and all such polynomials, the area is at least $\delta \cdot n^{-\kappa}$.

The lower bound $\gg n^{-4}$ follows from a result of Pommerenke [Po61].
The stronger lower bound $\gg (\log n)^{-1}$ was proved by Krishnapur, Lundberg,
and Ramachandran [KLR25], which in particular settles this conjecture.

Pólya [Po28] showed the area is always at most $\pi$, with equality only when all
roots are equal. Wagner [Wa88] showed the existence of polynomials with measure
$\ll_\varepsilon (\log \log n)^{-1/2+\varepsilon}$, providing a near-tight upper bound.
-/
@[category research solved, AMS 28 30]
theorem erdos_116 : answer(True) ↔
    ∃ (κ δ : ℝ), 0 < δ ∧ 0 < κ ∧
    ∀ (n : ℕ), 1 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ * (n : ℝ) ^ (-κ)) ≤
      volume (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) := by
  sorry

/--
Stronger logarithmic lower bound for the lemniscate area (Problem #116) [KLR25]:

Krishnapur, Lundberg, and Ramachandran proved that the area of the lemniscate interior
$\{z : |p(z)| < 1\}$ of a degree-$n$ monic polynomial with roots in the unit disk satisfies
$$
  |\{z : |p(z)| < 1\}| \gg (\log n)^{-\gamma}
$$
for some universal constant $\gamma > 0$. In fact, they show $\gamma = 1$ suffices.
This is strictly stronger than the polynomial bound `erdos_116` and captures
the main result of [KLR25].
-/
@[category research solved, AMS 28 30]
theorem erdos_116_log_lower_bound :
    ∃ (γ δ : ℝ), 0 < δ ∧ 0 < γ ∧
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ * (Real.log n) ^ (-γ)) ≤
      volume (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) := by
  sorry

end Erdos116

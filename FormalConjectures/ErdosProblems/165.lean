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
# Erdős Problem 165

*References:*
- [erdosproblems.com/165](https://www.erdosproblems.com/165)
- [Sh83] J. Shearer, *A note on the independence number of triangle-free graphs*,
  Discrete Math. 46 (1983), 83–87.
- [AKS80] M. Ajtai, J. Komlós and E. Szemerédi, *A note on Ramsey numbers*,
  J. Combin. Theory Ser. A 29 (1980), 354–360.
- [Ki95] J. H. Kim, *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$*,
  Random Structures Algorithms 7 (1995), 173–207.
- [BoKe21] T. Bohman and P. Keevash, *Dynamic concentration of the triangle-free process*,
  Random Structures Algorithms 58 (2021), 221–293.
- [PGM20] G. Fiz Pontiveros, S. Griffiths and R. Morris, *The triangle-free process and the
  Ramsey number $R(3,k)$*, Mem. Amer. Math. Soc. 263 (2020), no. 1274, v+125.
- [CJMS25] M. Campos, M. Jenssen, M. Michelen and J. Sahasrabudhe, *A new lower bound for
  the Ramsey numbers $R(3,k)$*, arXiv:2505.13371 (2025).
- [HHKP25] Z. Hefty, P. Horn, D. King and F. Pfender, *Improving $R(3,k)$ in just two bites*,
  arXiv:2510.19718 (2025).
-/

@[expose] public section

namespace Erdos165

open Filter Real Topology
open scoped Asymptotics

local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

def erdos_165.answer : ℕ → ℝ := sorry

/-- Give an asymptotic formula for $R(3,k)$. -/
@[category research open, question value, AMS 5]
theorem erdos_165 :
    (fun k : ℕ ↦ (R(3, k) : ℝ)) ~[atTop] erdos_165.answer := by
  sorry

/-- Does the normalised Ramsey number converge to a positive constant? -/
@[category research open, question, AMS 5]
theorem erdos_165.variants.limit_exists : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 c) := by
  sorry

/--
Shearer's upper bound [Sh83]: $R(3,k) \leq (1 + o(1)) k^2 / \log k$, i.e.
$$\limsup_{k \to \infty} \frac{R(3,k) \log k}{k^2} \leq 1.$$
This improved an earlier bound of Ajtai, Komlós and Szemerédi [AKS80].
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.shearer_upper :
    limsup (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop ≤ 1 := by
  sorry

/--
Kim's lower bound [Ki95]: $R(3,k) \geq (c + o(1)) k^2 / \log k$ for some constant $c > 0$
(Kim's original proof gave $c = 1/162$). Together with Shearer's upper bound this settled
the order of magnitude of $R(3,k)$.
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.kim_lower :
    ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The triangle-free process lower bound, proved independently by Bohman–Keevash [BoKe21] and
Fiz Pontiveros–Griffiths–Morris [PGM20]:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{4}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_quarter :
    (1 : ℝ) / 4 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The Campos–Jenssen–Michelen–Sahasrabudhe lower bound [CJMS25]:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_third :
    (1 : ℝ) / 3 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
The Hefty–Horn–King–Pfender lower bound [HHKP25], the current record:
$$\liminf_{k \to \infty} \frac{R(3,k) \log k}{k^2} \geq \frac{1}{2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.lower_bound_half :
    (1 : ℝ) / 2 ≤ liminf (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop := by
  sorry

/--
Fiz Pontiveros–Griffiths–Morris [PGM20] conjectured that the triangle-free process lower
bound $1/4$ gives the correct constant, i.e. that $R(3,k) \log k / k^2 \to 1/4$. This was
disproved by the lower bound $\liminf \geq 1/3$ of [CJMS25] (and a fortiori by
$\liminf \geq 1/2$ of [HHKP25]).
-/
@[category research solved, AMS 5]
theorem erdos_165.variants.limit_not_quarter :
    ¬ Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 (1 / 4)) := by
  sorry

/--
Is $c = 1/2$ the correct asymptotic, i.e. does
$$\lim_{k \to \infty} \frac{R(3,k) \log k}{k^2} = \frac{1}{2}?$$
This is conjectured in both [CJMS25] and [HHKP25].
-/
@[category research open, AMS 5]
theorem erdos_165.variants.limit_eq_half :
    Tendsto (fun k : ℕ ↦ (R(3, k) : ℝ) * log k / k ^ 2) atTop (𝓝 (1 / 2)) := by
  sorry

/-- The empty independent set gives $R(3,0)=0$. -/
@[category test, AMS 5]
theorem classicalRamsey_three_zero : R(3, 0) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  exact Or.inl fun _ ↦ Or.inr SimpleGraph.IsContained.of_isEmpty

/-- Every graph on one vertex contains an independent set of size one. -/
@[category test, AMS 5]
theorem classicalRamsey_three_one_le : R(3, 1) ≤ 1 := by
  apply Nat.sInf_le
  intro G
  refine Or.inr (SimpleGraph.IsContained.of_le ?_)
  intro x y h
  exact (h (Subsingleton.elim x y)).elim

end Erdos165

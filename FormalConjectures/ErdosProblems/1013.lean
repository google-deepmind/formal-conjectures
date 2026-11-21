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
# Erdős Problem 1013

*References:*
- [erdosproblems.com/1013](https://www.erdosproblems.com/1013)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GrYa68] Graver, J. E. and Yackel, J., *Some graph theoretic results associated with Ramsey's
  theorem*. J. Combinatorial Theory 4 (1968), 125-175.
- [DaIl22] Davies, E. and Illingworth, F., *The $\chi$-Ramsey problem for triangle-free graphs*.
  SIAM J. Discrete Math. 36 (2022), 1124-1134.
- [HHKP25] Hefty, Z., Horn, P., King, D. and Pfender, F., *Improving $R(3,k)$ in just two bites*.
  [arXiv:2510.19718](https://arxiv.org/abs/2510.19718) (2025).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1013

/-- $h_3(k)$ is the least $n$ such that some triangle-free graph on $n$ vertices has chromatic
number $k$. Triangle-free graphs of every chromatic number exist (Mycielski), so the set is
nonempty and `sInf` is a true minimum. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}

/-- A triangle-free graph on $m$ vertices with chromatic number $k$ gives $h_3(k) \leq m$. -/
@[category API, AMS 5]
theorem h3_le {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3)
    (hk : G.chromaticNumber = k) : h3 k ≤ m :=
  Nat.sInf_le ⟨G, hG, hk⟩

/-- The graph on one vertex is triangle-free with chromatic number $1$, so $h_3(1) \leq 1$. -/
@[category test, AMS 5]
theorem h3_one_le : h3 1 ≤ 1 :=
  h3_le (⊥ : SimpleGraph (Fin 1)) (SimpleGraph.cliqueFree_bot (by norm_num))
    (by exact_mod_cast SimpleGraph.chromaticNumber_bot (V := Fin 1))

def erdos_1013.parts.i.answer : ℕ → ℝ := sorry

/--
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with
chromatic number $k$. Find an asymptotic for $h_3(k)$, and also prove
$$\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.$$

This is the first part.
-/
@[category research open, question value, AMS 5]
theorem erdos_1013.parts.i :
    (fun k ↦ (h3 k : ℝ)) ~[atTop] erdos_1013.parts.i.answer := by
  sorry

/--
Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices with
chromatic number $k$. Find an asymptotic for $h_3(k)$, and also prove
$$\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.$$

This is the second part.
-/
@[category research open, AMS 5]
theorem erdos_1013.parts.ii :
    Tendsto (fun k : ℕ ↦ (h3 (k + 1) : ℝ) / h3 k) atTop (nhds 1) := by
  sorry

/--
Graver and Yackel [GrYa68] proved
$$h_3(k)\gg \frac{\log k}{\log\log k}k^2.$$
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.graver_yackel :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      c * (Real.log k / Real.log (Real.log k)) * k ^ 2 ≤ (h3 k : ℝ) := by
  sorry

/--
The upper bound $f(n) \leq (2+o(1))(n/\log n)^{1/2}$ of Davies and Illingworth [DaIl22] for the
function $f$ of [1104] gives
$$\left(\frac{1}{2}-o(1)\right)k^2\log k\leq h_3(k).$$
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.lower :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (1 / 2 - ε) * k ^ 2 * Real.log k ≤ (h3 k : ℝ) := by
  sorry

/--
The lower bound $f(n) \geq (1-o(1))(n/\log n)^{1/2}$ for the function $f$ of [1104], which follows
from the construction of Hefty, Horn, King, and Pfender [HHKP25], gives
$$h_3(k) \leq (2+o(1))k^2\log k.$$
The site states $(1+o(1))k^2\log k$, but the bounds recorded in [1104] give only $2+o(1)$.
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (h3 k : ℝ) ≤ (2 + ε) * k ^ 2 * Real.log k := by
  sorry

end Erdos1013

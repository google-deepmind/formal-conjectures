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

import FormalConjecturesUtil

/-!
# Erdős Problem 1153

*References:*
- [erdosproblems.com/1153](https://www.erdosproblems.com/1153)
- [Er61] Erdős, P., Problems and results on the theory of interpolation. II, Acta Math. Acad.
  Sci. Hungar. (1961), 235-244.
- [Be31] Bernstein, S., Sur la limitation des valeurs d'un polynôme $P_n(x)$ de degré $n$ sur
  tout un segment par ses valeurs en $n+1$ points du segment, Izv. Akad. Nauk SSSR (1931),
  1025-1050.
-/

open Filter Real Set

namespace Erdos1153

/--
The Lebesgue function of the interpolation nodes $x_1,\ldots,x_n$, that is
$$\lambda(t)=\sum_{k}\lvert \ell_k(t)\rvert,$$
where $\ell_k(t)=\prod_{i\neq k}\frac{t-x_i}{x_k-x_i}$ is the Lagrange basis polynomial
attached to the node $x_k$.
-/
noncomputable def lebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, |(Lagrange.basis Finset.univ x k).eval t|

/-- At any node the Lebesgue function takes the value $1$, since $\ell_k(x_k)=1$ and
$\ell_j(x_k)=0$ for $j\neq k$. -/
@[category API, AMS 41]
theorem lebesgueFunction_apply_node {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (k : Fin n) : lebesgueFunction x (x k) = 1 := by
  rw [lebesgueFunction, Finset.sum_eq_single k
    (fun j _ hjk => by rw [Lagrange.eval_basis_of_ne hjk (Finset.mem_univ k), abs_zero])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ k), abs_one]

/-- With a single node the Lebesgue function is constantly $1$. -/
@[category test, AMS 41]
theorem lebesgueFunction_singleton (x : Fin 1 → ℝ) (t : ℝ) : lebesgueFunction x t = 1 := by
  simp [lebesgueFunction, Finset.univ_unique, Lagrange.basis_singleton]

/--
Is it true that, for any fixed $-1\leq a<b\leq 1$,
$$\max_{t\in [a,b]}\lambda(t) > \left(\frac{2}{\pi}-o(1)\right)\log n?$$

Here $\lambda$ is the Lebesgue function of $n$ distinct nodes $x_1,\ldots,x_n\in [-1,1]$, and
the bound is asked to hold for every choice of such nodes.
-/
@[category research open, AMS 26 41]
theorem erdos_1153 :
    answer(sorry) ↔
      ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 → ∀ ε > (0 : ℝ),
        ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
          (∀ k, x k ∈ Icc (-1 : ℝ) 1) →
            ∃ t ∈ Icc a b, (2 / π - ε) * log n < lebesgueFunction x t := by
  sorry

/--
Bernstein [Be31] proved the case $a=-1$, $b=1$, and Erdős [Er61] improved it to
$$\max_{t\in [-1,1]}\lambda(t) > \frac{2}{\pi}\log n - O(1).$$
-/
@[category research solved, AMS 26 41]
theorem erdos_1153.variants.full_interval :
    ∃ C : ℝ, ∀ n : ℕ, ∀ x : Fin n → ℝ, Function.Injective x →
      (∀ k, x k ∈ Icc (-1 : ℝ) 1) →
        ∃ t ∈ Icc (-1 : ℝ) 1, 2 / π * log n - C < lebesgueFunction x t := by
  sorry

/--
The bound in `erdos_1153.variants.full_interval` is best possible: taking the nodes to be the
roots of the $n$th Chebyshev polynomial yields
$$\max_{t\in [-1,1]}\lambda(t) < \frac{2}{\pi}\log n + O(1).$$
-/
@[category research solved, AMS 26 41]
theorem erdos_1153.variants.best_possible :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → ∃ x : Fin n → ℝ, Function.Injective x ∧
      (∀ k, x k ∈ Icc (-1 : ℝ) 1) ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, lebesgueFunction x t < 2 / π * log n + C := by
  sorry

end Erdos1153

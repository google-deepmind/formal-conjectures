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
# Erdős Problem 1152

*References:*
- [erdosproblems.com/1152](https://www.erdosproblems.com/1152)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
- [EKS89] Erdős, P. and Kroó, A. and Szabados, J., *On convergent interpolatory polynomials*.
  J. Approx. Theory (1989), 232--241.
-/

open Filter Set MeasureTheory Topology

namespace Erdos1152

/--
For $n\geq 1$ fix some sequence of $n$ distinct numbers $x_{1n},\ldots,x_{nn}\in [-1,1]$. Let
$\epsilon=\epsilon(n)\to 0$.

Does there always exist a continuous function $f:[-1,1]\to \mathbb{R}$ such that if $p_n$ is a
sequence of polynomials, with degrees $\deg p_n<(1+\epsilon(n))n$, such that $p_n(x_{kn})=f(x_{kn})$
for all $1\leq k\leq n$, then $p_n(x)\not\to f(x)$ for almost all $x\in [-1,1]$?
-/
@[category research open, AMS 28 40 41]
theorem erdos_1152 :
    answer(sorry) ↔
    ∀ (x : (n : ℕ) → Fin n → Icc (-1 : ℝ) 1),
      (∀ n, Function.Injective (x n)) →
      ∀ (ε : ℕ → ℝ), (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
      ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) ∧
        ∀ (p : ℕ → Polynomial ℝ),
          (∀ n ≥ 1, ((p n).natDegree : ℝ) < (1 + ε n) * n ∧
            ∀ k : Fin n, (p n).eval (x n k : ℝ) = f (x n k : ℝ)) →
          ∀ᵐ t ∂volume.restrict (Icc (-1 : ℝ) 1),
            ¬ Tendsto (fun n : ℕ ↦ (p n).eval t) atTop (𝓝 (f t)) := by
  sorry

/--
Erdős, Kroó, and Szabados [EKS89] proved that, if $\epsilon>0$ is fixed and does not $\to 0$, then
there exist sequences $x_{ij}$ such that, for any continuous function $f$, there exists a sequence
of polynomials $p_n$, with degrees $\deg p_n<(1+\epsilon)n$, such that $p_n(x_{kn})=f(x_{kn})$ for
all $1\leq k\leq n$, and $p_n(x)\to f(x)$ uniformly for all $x\in [-1,1]$.
-/
@[category research solved, AMS 28 40 41]
theorem erdos_1152.variants.eks {ε : ℝ} (hε : 0 < ε) :
    ∃ x : (n : ℕ) → Fin n → Icc (-1 : ℝ) 1,
      (∀ n, Function.Injective (x n)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ p : ℕ → Polynomial ℝ,
          (∀ n ≥ 1, ((p n).natDegree : ℝ) < (1 + ε) * n ∧
            ∀ k : Fin n, (p n).eval (x n k : ℝ) = f (x n k : ℝ)) ∧
          TendstoUniformlyOn (fun n t ↦ (p n).eval t) f atTop (Icc (-1) 1) := by
  sorry

end Erdos1152

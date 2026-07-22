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
# Erdős Problem 1028

*References:*
- [erdosproblems.com/1028](https://www.erdosproblems.com/1028)
- [Er63d] Erdős, Pál, *On combinatorial questions connected with a theorem of Ramsey and van der
  Waerden*. Mat. Lapok (1963), 29-37.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [ErSp71] Erdős, P. and Spencer, J., *Imbalances in $k$-colorations*. Networks (1971/72),
  379-385.
-/

open Filter Asymptotics

namespace Erdos1028

/-- The imbalance of a finite set `X` under a colouring `f`, that is,
$\left\lvert \sum_{x<y\in X} f(x,y)\right\rvert$. -/
def imbalance (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|

/-- `H n` is the minimum, over all colourings `f` of pairs from `{1, …, n}` with values in
`{-1, 1}`, of the largest imbalance of a subset `X ⊆ {1, …, n}`. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {m | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)}

/--
Let
\[H(n)=\min_f \max_{X\subseteq \{1,\ldots,n\}} \left\lvert \sum_{x<y\in X} f(x,y)\right\rvert,\]
where $f$ ranges over all functions $f:\{1,\ldots,n\}^2\to \{-1,1\}$. Estimate $H(n)$.

Erdős [Er63d] proved
\[\frac{n}{4}\leq H(n) \ll n^{3/2}.\]
Erdős and Spencer [ErSp71] proved that $H(n)\gg n^{3/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1028 :
    (fun n => (H n : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/-- Erdős [Er63d] proved
\[\frac{n}{4}\leq H(n) \ll n^{3/2}.\] -/
@[category research solved, AMS 5]
theorem erdos_1028.variants.lower_bound :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ (H n : ℝ) := by
  sorry

/-- Erdős [Er63d] proved
\[\frac{n}{4}\leq H(n) \ll n^{3/2}.\] -/
@[category research solved, AMS 5]
theorem erdos_1028.variants.upper_bound :
    (fun n => (H n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/-- Erdős and Spencer [ErSp71] proved that $H(n)\gg n^{3/2}$. -/
@[category research solved, AMS 5]
theorem erdos_1028.variants.erdos_spencer :
    (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) =O[atTop] (fun n => (H n : ℝ)) := by
  sorry

end Erdos1028

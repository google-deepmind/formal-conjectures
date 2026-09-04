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
# Erdős Problem 793

*References:*
- [erdosproblems.com/793](https://www.erdosproblems.com/793)
- [Er38] P. Erdős, On sequences of integers no one of which divides the product of two
  others and on related problems. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.
- [Er69] Erdős, Paul, Some applications of graph theory to number theory. The Many Facets of
  Graph Theory (Proc. Conf., Western Mich. Univ., Kalamazoo, Mich., 1968) (1969), 77-82.
-/

open Nat Filter Real Set
open scoped Topology Asymptotics Classical

namespace Erdos793

local notation "π" => primeCounting

/--
Let $F(n)$ be the maximum possible size of a subset $A\subseteq\{1,\ldots,n\}$ such
that $a\nmid bc$ whenever $a,b,c\in A$ with $a\neq b$ and $a\neq c$.
-/
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A =>
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → ¬(a ∣ b * c)).sup Finset.card

/--
Is there a constant $C$ such that $F(n)=\pi(n)+(C+o(1))n^{2/3}(\log n)^{-2}$?
-/
@[category research open, AMS 11]
theorem erdos_793 :
    answer(sorry) ↔ ∃ (C : ℝ) (o : ℕ → ℝ),
      o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (F n : ℝ) = (π n : ℝ) + (C + o n) * (n : ℝ) ^ (2 / 3 : ℝ) / (Real.log n) ^ 2 := by
  sorry

/--
Erdős [Er38] proved there exist constants $0<c_1\leq c_2$ such that
$\pi(n)+c_1n^{2/3}(\log n)^{-2}\leq F(n) \leq \pi(n)+c_2n^{2/3}(\log n)^{-2}$.
-/
@[category research solved, AMS 11]
theorem erdos_793.variants.bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ᶠ n in atTop,
      (π n : ℝ) + c₁ * (n : ℝ) ^ (2 / 3 : ℝ) / (Real.log n) ^ 2 ≤ F n ∧
      (F n : ℝ) ≤ (π n : ℝ) + c₂ * (n : ℝ) ^ (2 / 3 : ℝ) / (Real.log n) ^ 2 := by
  sorry

/--
Erdős [Er69] gave a simple proof that $F(n) \leq \pi(n)+n^{2/3}$: define a graph with
vertex set the union of those integers in $[1,n^{2/3}]$ with all primes $p\in (n^{2/3},n]$.
We have an edge $u\sim v$ if and only if $uv\in A$. It is easy to see that every $m\leq n$
can be written as $uv$ where $u\leq n^{2/3}$ and $v$ is either prime or $\leq n^{2/3}$, and
hence there are $\geq \lvert A\rvert$ many edges. This graph contains no path of length
$3$ and hence must be a tree and have fewer edges than vertices, and we are done. This
can be improved to give the upper bound mentioned by using a subset of integers in
$[1,n^{2/3}]$.
-/
@[category research solved, AMS 11]
theorem erdos_793.variants.simple_upper_bound :
    ∀ n : ℕ, (F n : ℝ) ≤ (π n : ℝ) + (n : ℝ) ^ (2 / 3 : ℝ) := by
  sorry

end Erdos793

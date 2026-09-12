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
# Erdős Problem 1016

*References:*
- [erdosproblems.com/1016](https://www.erdosproblems.com/1016)
- [Bo71] Bondy, J. A., *Pancyclic graphs. I*. J. Combinatorial Theory Ser. B (1971), 80--84.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GKW16] George, John C. and Khodkar, Abdollah and Wallis, W. D., *Pancyclic and bipancyclic
  graphs*. (2016), xii+108.
- [Gr13] S. Griffin, *Minimal Pancyclicity*. arXiv:1312.0274 (2013).
-/

open Filter SimpleGraph

namespace Erdos1016

/--
A graph contains a cycle on $k$ vertices for every $3\leq k\leq |V|$. Such graphs are called
pancyclic.
-/
def HasAllCycleLengths {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ k, 3 ≤ k → k ≤ Fintype.card V → cycleGraph k ⊑ G

/--
`h n` is the least `t` such that some graph on `n` vertices with `n + t` edges contains a cycle
on $k$ vertices for every $3\leq k\leq n$.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {t | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = n + t ∧ HasAllCycleLengths G}

/--
Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n+h(n)$ edges which contains
a cycle on $k$ vertices, for all $3\leq k\leq n$. Estimate $h(n)$. In particular, is it true that
$$h(n) \geq \log_2n+\log_*n-O(1),$$
where $\log_*n$ is the iterated logarithmic function?
-/
@[category research open, AMS 5]
theorem erdos_1016 : answer(sorry) ↔
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Real.logb 2 (n : ℝ) + (Real.iteratedLog (n : ℝ) : ℝ) - C ≤ (h n : ℝ) := by
  sorry

/--
Such graphs are called pancyclic. A problem of Bondy [Bo71], who claimed a proof (without details)
of
$$\log_2(n-1)-1\leq h(n).$$
A proof of the above lower bound is provided by Griffin [Gr13].
-/
@[category research solved, AMS 5]
theorem erdos_1016.variants.lower_bound :
    ∀ n : ℕ, 2 ≤ n → Real.logb 2 ((n : ℝ) - 1) - 1 ≤ (h n : ℝ) := by
  sorry

/--
Bondy [Bo71] claimed a proof (without details) of
$$h(n) \leq \log_2n+\log_*n+O(1).$$
The first published proof of the upper bound appears to be in Chapter 4.5 of George, Khodkar, and
Wallis [GKW16].
-/
@[category research solved, AMS 5]
theorem erdos_1016.variants.upper_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (h n : ℝ) ≤ Real.logb 2 (n : ℝ) + (Real.iteratedLog (n : ℝ) : ℝ) + C := by
  sorry

/--
Erdős [Er71] believed the upper bound is closer to the truth, but could not even prove
$h(n)-\log_2n\to \infty$.
-/
@[category research open, AMS 5]
theorem erdos_1016.variants.minus_log :
    Tendsto (fun n : ℕ ↦ (h n : ℝ) - Real.logb 2 (n : ℝ)) atTop atTop := by
  sorry

end Erdos1016

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
# Erdős Problem 626

*Reference:* [erdosproblems.com/626](https://www.erdosproblems.com/626)

Let $k \geq 4$ and $g_k(n)$ denote the largest $m$ such that there is a graph on $n$ vertices
with chromatic number $k$ and girth $> m$. Does
$$
  \lim_{n \to \infty} g_k(n) / \log n
$$
exist?

Conversely, if $h^{(m)}(n)$ is the maximal chromatic number of a graph on $n$ vertices
with girth $> m$ then does
$$
  \lim_{n \to \infty} \log h^{(m)}(n) / \log n
$$
exist, and what is its value?

[Er59b] Erdős, P., _Graph theory and probability_, Canad. J. Math. **11** (1959), 34–38.

[Er62b] Erdős, P., _On circuits and subgraphs of chromatic graphs_, Mathematika **9** (1962),
170–175.

[Er69b] Erdős, P., _Problems and results in chromatic graph theory_, 1969.

[Ko88] Kostochka, A.V., _The minimum Hadwiger number for graphs with a given mean degree of
vertices_, Metody Diskret. Analiz. **38** (1988), 37–58.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos626

/-- $g_k(n)$ is the largest $m$ such that there exists a graph on $n$ vertices
    with chromatic number $k$ and girth $> m$. Returns $0$ if no such graph exists. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ m < G.girth}

/-- $h^{(m)}(n)$ is the maximal chromatic number of a graph on $n$ vertices
    with girth $> m$. -/
noncomputable def h (m n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ m < G.girth}

/--
**Erdős Problem 626, Part 1** [Er59b][Er62b][Er69b]:

For $k \geq 4$, does the limit $\lim_{n \to \infty} g_k(n) / \log n$ exist?

It is known that
$$
  \frac{1}{4 \log k} \log n \leq g_k(n) \leq \frac{2}{\log(k-2)} \log n + 1,
$$
the lower bound due to Kostochka [Ko88] and the upper bound to Erdős [Er59b].
-/
@[category research open, AMS 5]
theorem erdos_626 : answer(sorry) ↔
    ∀ k : ℕ, k ≥ 4 → ∃ L : ℝ,
      Tendsto (fun n : ℕ => (g k n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) := by
  sorry

/--
**Erdős Problem 626, Part 2** [Er59b][Er62b][Er69b]:

For $m \geq 1$, does the limit $\lim_{n \to \infty} \log h^{(m)}(n) / \log n$ exist,
and what is its value?

Erdős [Er59b] proved that
$$
  \lim_{n \to \infty} \frac{\log h^{(m)}(n)}{\log n} \gg \frac{1}{m}
$$
and, for odd $m$,
$$
  \lim_{n \to \infty} \frac{\log h^{(m)}(n)}{\log n} \leq \frac{2}{m+1},
$$
and conjectured this is sharp.
-/
@[category research open, AMS 5]
theorem erdos_626.variants.maximal_chromatic : answer(sorry) ↔
    ∀ m : ℕ, m ≥ 1 → ∃ L : ℝ,
      Tendsto (fun n : ℕ => Real.log (h m n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) := by
  sorry

/--
**Erdős Problem 626, Odd sharpness variant** [Er59b]:

For odd $m$, Erdős proved $\lim_{n \to \infty} \log h^{(m)}(n) / \log n \leq \frac{2}{m+1}$
and conjectured this bound is sharp, i.e., the limit equals $\frac{2}{m+1}$.
-/
@[category research open, AMS 5]
theorem erdos_626.variants.odd_sharpness :
    ∀ m : ℕ, Odd m → ∃ L : ℝ,
      Tendsto (fun n : ℕ => Real.log (h m n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) ∧
      L = 2 / (m + 1 : ℝ) := by
  sorry

/--
**Erdős Problem 626, Even $m$ variant** [Er59b]:

For even $m$, Erdős suspected the limit $\lim_{n \to \infty} \log h^{(m)}(n) / \log n$
lies in the interval $\left[\frac{2}{m+2}, \frac{2}{m}\right]$.
-/
@[category research open, AMS 5]
theorem erdos_626.variants.even_bounds :
    ∀ m : ℕ, Even m → 0 < m → ∃ L : ℝ,
      Tendsto (fun n : ℕ => Real.log (h m n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) ∧
      2 / (m + 2 : ℝ) ≤ L ∧ L ≤ 2 / (m : ℝ) := by
  sorry

end Erdos626

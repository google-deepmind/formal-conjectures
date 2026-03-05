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
# Erdős Problem 627

*Reference:* [erdosproblems.com/627](https://www.erdosproblems.com/627)

Let $\omega(G)$ denote the clique number of $G$ and $\chi(G)$ the chromatic number. If $f(n)$ is the
maximum value of $\chi(G)/\omega(G)$, as $G$ ranges over all graphs on $n$ vertices, then does
$$\lim_{n \to \infty} \frac{f(n)}{n / (\log_2 n)^2}$$
exist?

Erdős [Er67c] proved that $f(n) \asymp n / (\log_2 n)^2$ and that the limit, if it exists,
must be in $[1/4, 4]$.
-/

open SimpleGraph Filter

open scoped Topology

namespace Erdos627

/-- The chromatic number of a simple graph on `Fin n`: the minimum number of colors
    such that there exists a proper coloring. -/
noncomputable def chromaticNumber627 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ f : Fin n → Fin k, ∀ u v, G.Adj u v → f u ≠ f v}

/-- The clique number of a simple graph on `Fin n`: the maximum size of a clique. -/
noncomputable def cliqueNumber627 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ¬G.CliqueFree k}

/-- $f_{627}(n)$ is the maximum of $\chi(G)/\omega(G)$ over all simple graphs $G$
on $n$ vertices. -/
noncomputable def f627 (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ G : SimpleGraph (Fin n),
    cliqueNumber627 G > 0 ∧
    r = (chromaticNumber627 G : ℝ) / (cliqueNumber627 G : ℝ)}

/--
**Erdős Problem 627** [Er61d][Er67c][Er69b]:

Does the limit $\lim_{n \to \infty} f(n) / (n / (\log_2 n)^2)$ exist, where $f(n)$ is the maximum
of $\chi(G)/\omega(G)$ over all graphs $G$ on $n$ vertices?
-/
@[category research open, AMS 5]
theorem erdos_627 : answer(sorry) ↔
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => f627 n / ((n : ℝ) / (Real.logb 2 (n : ℝ)) ^ 2))
      atTop (nhds L) := by
  sorry

end Erdos627

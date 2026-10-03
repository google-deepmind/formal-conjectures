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
# Erdős Problem 626

*References:*
- [erdosproblems.com/626](https://www.erdosproblems.com/626)
- [Er59b] Erdős, P., *Graph theory and probability*. Canadian J. Math. (1959), 34-38.
- [Er62b] Erdős, P., *On circuits and subgraphs of chromatic graphs*. Mathematika (1962),
  170-175.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Ko88] Kostochka, A. V., *Upper bounds on the chromatic number of graphs*. Trudy Inst. Mat.
  (Novosibirsk) (1988), 204-226, 265.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos626

/--
`g k n` is $g_k(n)$: the largest $m$ such that some graph on $n$ vertices has chromatic number
exactly $k$ and girth $> m$, that is, no cycle of length $\leq m$.

The girth is `SimpleGraph.egirth`, which is `⊤` for an acyclic graph. The value `sSup ∅ = 0`
for $n < k$ affects only finitely many $n$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth}

/--
`h m n` is $h^{(m)}(n)$: the largest chromatic number of a graph on $n$ vertices with girth
$> m$.
-/
noncomputable def h (m n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c}

/-- Every cycle has length at least $3$, so for $m \leq 2$ the girth condition is vacuous and
$h^{(m)}(n) = n$. -/
@[category test, AMS 5]
theorem h_of_le_two (m n : ℕ) (hm : m ≤ 2) : h m n = n := by
  sorry

/--
Let $k \geq 4$ and let $g_k(n)$ denote the largest $m$ such that there is a graph on $n$
vertices with chromatic number $k$ and girth $> m$ (i.e. containing no cycle of length
$\leq m$). Does
$$\lim_{n\to\infty}\frac{g_k(n)}{\log n}$$
exist?

By `Erdos626.erdos_626.variants.kostochka` and `Erdos626.erdos_626.variants.erdos_upper`, the
limit, if it exists, is a positive real number.
-/
@[category research open, AMS 5]
theorem erdos_626.parts.i : answer(sorry) ↔
    ∀ k : ℕ, 4 ≤ k → ∃ L : ℝ,
      Tendsto (fun n : ℕ ↦ (g k n : ℝ) / Real.log n) atTop (𝓝 L) := by
  sorry

/--
Kostochka [Ko88] proved that for $k \geq 4$
$$g_k(n) \geq \frac{1}{4\log k}\log n.$$
The bound is usually stated for the girth itself, while $g_k(n)$ here is the largest $m$ below
the girth, so we state it with an $\varepsilon$ of slack: for every $\varepsilon > 0$ and all
sufficiently large $n$,
$g_k(n) \geq \left(\frac{1}{4\log k} - \varepsilon\right)\log n$.
-/
@[category research solved, AMS 5]
theorem erdos_626.variants.kostochka :
    ∀ k : ℕ, 4 ≤ k → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 / (4 * Real.log k) - ε) * Real.log n ≤ (g k n : ℝ) := by
  sorry

/--
Erdős [Er59b] proved that for $k \geq 4$
$$g_k(n) \leq \frac{2}{\log(k-2)}\log n + 1.$$
We state it for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_626.variants.erdos_upper :
    ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in atTop,
      (g k n : ℝ) ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 := by
  sorry

/--
Let $h^{(m)}(n)$ be the maximal chromatic number of a graph on $n$ vertices with girth $> m$.
Does
$$\lim_{n\to\infty}\frac{\log h^{(m)}(n)}{\log n}$$
exist, and what is its value? The value is asked for in
`Erdos626.erdos_626.variants.h_odd_conjecture` and `Erdos626.erdos_626.variants.h_even_conjecture`.
-/
@[category research open, AMS 5]
theorem erdos_626.parts.ii : answer(sorry) ↔
    ∀ m : ℕ, ∃ L : ℝ,
      Tendsto (fun n : ℕ ↦ Real.log (h m n : ℝ) / Real.log n) atTop (𝓝 L) := by
  sorry

/--
Erdős [Er59b] proved that
$$\lim_{n\to\infty}\frac{\log h^{(m)}(n)}{\log n} \gg \frac{1}{m}.$$
The existence of the limit is open, so we state the lower bound for the lower limit: there is
an absolute constant $c > 0$ such that for every $m \geq 1$ and $\varepsilon > 0$, eventually
$h^{(m)}(n) \geq n^{c/m - \varepsilon}$.
-/
@[category research solved, AMS 5]
theorem erdos_626.variants.h_lower :
    ∃ c > (0 : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (c / (m : ℝ) - ε) ≤ (h m n : ℝ) := by
  sorry

/--
Erdős [Er59b] proved that for odd $m$
$$\lim_{n\to\infty}\frac{\log h^{(m)}(n)}{\log n} \leq \frac{2}{m+1}.$$
The existence of the limit is open, so we state the bound for the upper limit: for every
$\varepsilon > 0$, eventually $h^{(m)}(n) \leq n^{2/(m+1) + \varepsilon}$.
-/
@[category research solved, AMS 5]
theorem erdos_626.variants.h_upper_odd :
    ∀ m : ℕ, Odd m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (h m n : ℝ) ≤ (n : ℝ) ^ (2 / ((m : ℝ) + 1) + ε) := by
  sorry

/--
Erdős conjectured that the bound in `Erdos626.erdos_626.variants.h_upper_odd` is sharp: for
odd $m$,
$$\lim_{n\to\infty}\frac{\log h^{(m)}(n)}{\log n} = \frac{2}{m+1}.$$
-/
@[category research open, AMS 5]
theorem erdos_626.variants.h_odd_conjecture :
    ∀ m : ℕ, Odd m → Tendsto (fun n : ℕ ↦ Real.log (h m n : ℝ) / Real.log n) atTop
      (𝓝 (2 / ((m : ℝ) + 1))) := by
  sorry

/--
For even $m$, Erdős had no good guess for the value of the limit, other than that it should
lie in $\left[\frac{2}{m+2}, \frac{2}{m}\right]$. He could not prove this even for $m = 4$.

The existence of the limit is open, so we state the claim for the lower and upper limits: for
every $\varepsilon > 0$, eventually
$n^{2/(m+2) - \varepsilon} \leq h^{(m)}(n) \leq n^{2/m + \varepsilon}$. We require $m \geq 2$,
since $2/m$ is undefined for $m = 0$. The upper half is known: girth $> m$ implies girth
$> m - 1$, so $h^{(m)}(n) \leq h^{(m-1)}(n)$, and `Erdos626.erdos_626.variants.h_upper_odd` for
the odd number $m - 1$ gives the exponent $2/m$.
-/
@[category research open, AMS 5]
theorem erdos_626.variants.h_even_conjecture :
    ∀ m : ℕ, Even m → 2 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (2 / ((m : ℝ) + 2) - ε) ≤ (h m n : ℝ) ∧
        (h m n : ℝ) ≤ (n : ℝ) ^ (2 / (m : ℝ) + ε) := by
  sorry

end Erdos626

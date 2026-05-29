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
# Erdős Problem 1156

*Reference:* [erdosproblems.com/1156](https://www.erdosproblems.com/1156)

Let $G$ be a random graph on $n$ vertices, in which every edge is included
independently with probability $1/2$ (the Erdős–Rényi model $G(n, 1/2)$).

Bollobás [Bo88] proved that $\chi(G) \sim n / (2 \log_2 n)$ with high probability.
Shamir and Spencer [ShSp87] proved concentration within $o(\sqrt{n})$.
Heckel and Riordan [HeRi23] proved concentration cannot be within $n^c$ for $c < 1/2$.

[AlSp92] Alon, N. and Spencer, J., _The Probabilistic Method_, Wiley, 1992.

[AlSp16] Alon, N. and Spencer, J. H., _The Probabilistic Method_, 4th ed., Wiley, 2016.

[Bo88] Bollobás, B., _The chromatic number of random graphs_. Combinatorica (1988), 49–55.

[He21] Heckel, A., _Non-concentration of the chromatic number of a random graph_.
J. Amer. Math. Soc. (2021), 245–260.

[HeRi23] Heckel, A. and Riordan, O., _How does the chromatic number of a random graph vary?_
J. Lond. Math. Soc. (2) (2023), 1769–1815.

[Sc17] Scott, A., _On the concentration of the chromatic number of random graphs_.
arXiv:0806.0178 (2017).

[ShSp87] Shamir, E. and Spencer, J., _Sharp concentration of the chromatic number on random
graphs $G_{n,p}$_. Combinatorica (1987), 121–129.

[Va99] Vu, V. H. (1999), 3.64.
-/

open Filter

open scoped Topology

namespace Erdos1156

/-- The probability that the chromatic number of a uniformly random graph
$G(n, 1/2)$ on $n$ vertices satisfies predicate $P$. Here $G(n, 1/2)$ is the
Erdős–Rényi model where each edge is included independently with
probability $1/2$, equivalently the uniform distribution over all simple
graphs on $n$ labelled vertices. -/
opaque chromaticNumberProb (n : ℕ) (P : ℕ → Prop) : ℝ

/--
Erdős Problem 1156, Part 1 [AlSp92]:

There exists a constant $C$ such that $\chi(G(n, 1/2))$ is almost surely concentrated
on at most $C$ values. That is, for every $\varepsilon > 0$ and all sufficiently large $n$,
there is a set $S$ of at most $C$ natural numbers with
$\mathbb{P}(\chi(G) \in S) \geq 1 - \varepsilon$.
-/
@[category research open, AMS 5 60]
theorem erdos_1156 :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ S : Finset ℕ, S.card ≤ C ∧
          chromaticNumberProb n (· ∈ S) ≥ 1 - ε := by
  sorry

/--
Erdős Problem 1156, Part 2 [AlSp92] [Va99]:

There exists a function $\omega : \mathbb{N} \to \mathbb{R}$ with $\omega(n) \to \infty$ such that
for every function $f : \mathbb{N} \to \mathbb{R}$, for all sufficiently large $n$,
$$
\mathbb{P}(|\chi(G) - f(n)| < \omega(n)) < 1/2.
$$
That is, the chromatic number cannot be concentrated in any interval of width
$2\omega(n)$ with probability $\geq 1/2$.
-/
@[category research open, AMS 5 60]
theorem erdos_1156.variants.anticoncentration :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ f : ℕ → ℝ, ∀ᶠ n in atTop,
        chromaticNumberProb n (fun k => |(k : ℝ) - f n| < ω n) < 1 / 2 := by
  sorry

end Erdos1156

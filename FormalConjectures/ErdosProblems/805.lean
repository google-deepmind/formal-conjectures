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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 805

*Reference:* [erdosproblems.com/805](https://www.erdosproblems.com/805)

For which functions $g(n)$ with $n > g(n) \geq (\log n)^2$ is there a graph on $n$ vertices
in which every induced subgraph on $g(n)$ vertices contains a clique of size $\geq \log n$
and an independent set of size $\geq \log n$?

In particular, is there such a graph for $g(n) = (\log n)^3$?

See also [Problem #804](https://www.erdosproblems.com/804).

Additional thanks to Zach Hunter.

[Er91] Erdős, P., _Problems and results in combinatorial number theory_.

[AlSu07] Alon, N. and Sudakov, B., _On graphs with subgraphs having large independence
numbers_. J. Graph Theory (2007), 149-157.

[ABS21] Alon, N., Bucić, M. and Sudakov, B., _Large cliques and independent sets all over
the place_. Proc. Amer. Math. Soc. (2021), 3145-3157.
-/

open SimpleGraph Finset

namespace Erdos805

/-- The Erdős–Hajnal property for Problem 805: a graph $G$ on $\operatorname{Fin}(n)$ has
    the property that every induced subgraph on $m$ vertices contains both a clique and an
    independent set of size at least $k$.

    Note: This is distinct from the more famous "Erdős–Hajnal conjecture" about hereditary
    graph properties and polynomial Ramsey numbers. -/
def ErdosHajnalProperty {n : ℕ} (G : SimpleGraph (Fin n)) (m k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m →
    (∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ k ∧ G.IsClique ↑T) ∧
    (∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ k ∧ G.IsIndepSet ↑T)

/--
Erdős–Hajnal conjecture [Er91]: is there a graph on $n$ vertices such that every
induced subgraph on $\lfloor (\log n)^3 \rfloor$ vertices contains both a clique and an
independent set of size $\geq \lceil \log n \rceil$?

Erdős and Hajnal conjectured that the answer is no.
-/
@[category research open, AMS 5]
theorem erdos_805 : answer(sorry) ↔
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ G : SimpleGraph (Fin n), ErdosHajnalProperty G
        (Nat.floor ((Real.log (n : ℝ)) ^ 3))
        (Nat.ceil (Real.log (n : ℝ))) := by
  sorry

/--
Alon–Sudakov [AlSu07]: there is no such graph with
$g(n) = c \cdot (\log n)^3 / \log(\log n)$ for some constant $c > 0$.
This is a partial result toward the Erdős–Hajnal conjecture.
-/
@[category research solved, AMS 5]
theorem erdos_805.variants.alon_sudakov :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ¬∃ G : SimpleGraph (Fin n), ErdosHajnalProperty G
        (Nat.floor (c * (Real.log (n : ℝ)) ^ 3 / Real.log (Real.log (n : ℝ))))
        (Nat.ceil (Real.log (n : ℝ))) := by
  sorry

/--
Alon–Bucić–Sudakov [ABS21]: for every $\varepsilon > 0$, for sufficiently large $n$,
there exists a graph on $n$ vertices satisfying the property with
$g(n) = \lfloor 2^{2^{(\log \log n)^{1/2+\varepsilon}}} \rfloor$.
-/
@[category research solved, AMS 5]
theorem erdos_805.variants.alon_bucic_sudakov :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ G : SimpleGraph (Fin n), ErdosHajnalProperty G
          (Nat.floor ((2 : ℝ) ^ ((2 : ℝ) ^ ((Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2 + ε)))))
          (Nat.ceil (Real.log (n : ℝ))) := by
  sorry

end Erdos805

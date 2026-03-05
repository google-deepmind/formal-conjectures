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
# Erdős Problem 615

*Reference:* [erdosproblems.com/615](https://www.erdosproblems.com/615)

Does there exist some constant $c > 0$ such that if $G$ is a graph with $n$ vertices
and $\geq (1/8 - c)n^2$ edges then $G$ must contain either a $K_4$ or an independent set
on at least $n / \log n$ vertices?

Equivalently, if $\mathrm{rt}(n; k, \ell)$ denotes the Ramsey-Turán number (maximum number of
edges in a $K_k$-free graph on $n$ vertices with independence number $< \ell$), the
question asks whether $\mathrm{rt}(n; 4, \lceil n / \log n \rceil) < (1/8 - c)n^2$ for some
$c > 0$.

A problem of Erdős, Hajnal, Simonovits, Sós, and Szemerédi [EHSSS93].

Erdős, Hajnal, Sós, and Szemerédi [EHSS83] proved that for any fixed $\varepsilon > 0$,
$$\mathrm{rt}(n; 4, \varepsilon n) < (1/8 + o(1))n^2.$$

Sudakov [Su03] proved that $\mathrm{rt}(n; 4, n \cdot e^{-f(n)}) = o(n^2)$ whenever
$f(n)/\sqrt{\log n} \to \infty$.

Disproved by Fox, Loh, and Zhao [FLZ15], who showed that
$\mathrm{rt}(n; 4, n \cdot e^{-f(n)}) \geq (1/8 - o(1))n^2$
whenever $f(n) = o(\sqrt{\log n / \log \log n})$.

**References:**

[EHSSS93] Erdős, P., Hajnal, A., Simonovits, M., Sós, V. T., and Szemerédi, E. (1993).

[EHSS83] Erdős, P., Hajnal, A., Sós, V. T., and Szemerédi, E. (1983).

[Su03] Sudakov, B. (2003).

[FLZ15] Fox, J., Loh, P.-S., and Zhao, Y. (2015).
-/

open SimpleGraph Classical

namespace Erdos615

/-- A set of vertices is independent in $G$ if no two distinct vertices in the set
    are adjacent. -/
def IsIndependentSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- The Ramsey-Turán number $\mathrm{rt}(n; k, \ell)$: the maximum number of edges in a graph
    on $n$ vertices that contains no $k$-clique and has no independent set of size
    $\geq \ell$. Returns $0$ if no such graph exists. -/
noncomputable def ramseyTuranNumber (n k ℓ : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.edgeFinset.card = m ∧ G.CliqueFree k ∧
    ∀ S : Finset (Fin n), IsIndependentSet G S → S.card < ℓ}

/--
**Erdős Problem 615** (DISPROVED) [EHSSS93]:

Does there exist $c > 0$ such that for all sufficiently large $n$, every graph $G$
on $n$ vertices with at least $(1/8 - c)n^2$ edges contains either a $K_4$ or an
independent set of size at least $n / \log n$?

Disproved by Fox, Loh, and Zhao [FLZ15].
-/
@[category research solved, AMS 5]
theorem erdos_615 : answer(False) ↔
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        (G.edgeFinset.card : ℝ) ≥ (1 / 8 - c) * (n : ℝ) ^ 2 →
        (¬G.CliqueFree 4) ∨
        ∃ S : Finset (Fin n), (S.card : ℝ) ≥ (n : ℝ) / Real.log (n : ℝ) ∧
          IsIndependentSet G S := by
  sorry

/--
**Erdős-Hajnal-Sós-Szemerédi** [EHSS83]:

For any fixed $\varepsilon > 0$, every $K_4$-free graph on $n$ vertices with independence
number $< \varepsilon n$ has fewer than $(1/8 + o(1))n^2$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_615.variants.EHSS (ε : ℝ) (hε : ε > 0) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 4 →
        (∀ S : Finset (Fin n), IsIndependentSet G S → (S.card : ℝ) < ε * (n : ℝ)) →
        (G.edgeFinset.card : ℝ) ≤ (1 / 8 + δ) * (n : ℝ) ^ 2 := by
  sorry

end Erdos615

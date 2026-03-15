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
# Erdős Problem 717

*Reference:* [erdosproblems.com/717](https://www.erdosproblems.com/717)

Let $G$ be a graph on $n$ vertices with chromatic number $\chi(G)$ and let $\sigma(G)$ be
the maximal $k$ such that $G$ contains a subdivision of $K_k$. Is it true that
$$\chi(G) \ll \frac{n^{1/2}}{\log n} \cdot \sigma(G)?$$

Hajós originally conjectured that $\chi(G) \leq \sigma(G)$, which was proved by Dirac [Di52]
when $\chi(G) = 4$. Catlin [Ca74] disproved Hajós' conjecture for all $\chi(G) \geq 7$, and
Erdős and Fajtlowicz [ErFa81] disproved it in a strong form, showing that for almost
all graphs on $n$ vertices, $\chi(G) \gg \frac{n^{1/2}}{\log n} \cdot \sigma(G)$.

The answer is yes, proved by Fox, Lee, and Sudakov [FLS13].

[Di52] Dirac, G. A., _A property of 4-chromatic graphs and some remarks on critical graphs_.
J. London Math. Soc. **27** (1952), 85–92.

[Ca74] Catlin, P. A., _Subgraphs of graphs, I_. Discrete Mathematics **10** (1974), 225–233.

[ErFa81] Erdős, P. and Fajtlowicz, S., _On the conjecture of Hajós_. Combinatorica **1**
(1981), 141–143.

[FLS13] Fox, J., Lee, C., and Sudakov, B., _Chromatic number, clique subdivisions, and the
conjectures of Hajós and Erdős–Fajtlowicz_. Combinatorica **33** (2013), 181–197.
-/

open SimpleGraph

namespace Erdos717

/-- A graph $G$ contains a subdivision of $K_k$ (a topological $K_k$ minor) if there
    exist $k$ distinct branch vertices and internally vertex-disjoint paths in $G$
    between every pair of branch vertices. -/
def ContainsSubdivision {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k ↪ V)
    (paths : ∀ (i j : Fin k), i < j → G.Walk (f i) (f j)),
    -- Each walk is a path (no repeated vertices)
    (∀ i j (h : i < j), (paths i j h).IsPath) ∧
    -- Internal vertices of different paths are disjoint
    (∀ i₁ j₁ (h₁ : i₁ < j₁) i₂ j₂ (h₂ : i₂ < j₂),
      (i₁, j₁) ≠ (i₂, j₂) →
      ∀ v, v ∈ (paths i₁ j₁ h₁).support.tail.dropLast →
           v ∉ (paths i₂ j₂ h₂).support.tail.dropLast) ∧
    -- Internal vertices are disjoint from branch vertices
    (∀ i j (h : i < j) v,
      v ∈ (paths i j h).support.tail.dropLast →
      ∀ m : Fin k, v ≠ f m)

/-- $\sigma(G)$ is the maximum $k$ such that $G$ contains a subdivision of $K_k$.
    For a graph on a finite vertex type, this is always finite. -/
noncomputable def subdivisionNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ContainsSubdivision G k}

/--
**Erdős Problem 717** (PROVED, Fox–Lee–Sudakov [FLS13]):

For every graph $G$ on $n$ vertices,
$$\chi(G) \leq C \cdot \frac{\sqrt{n}}{\log n} \cdot \sigma(G)$$
for some absolute constant $C > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_717 : answer(True) ↔
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ), 2 ≤ n →
        ∀ (G : SimpleGraph (Fin n)),
          (G.chromaticNumber.toNat : ℝ) ≤
            C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) *
              (subdivisionNumber G : ℝ) := by
  sorry

end Erdos717

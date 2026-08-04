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
# Erdős Problem 180

*References:*
- [erdosproblems.com/180](https://www.erdosproblems.com/180)
- [ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica (1982), 275-288.
- [OpenAI26] OpenAI, *Ten advances in mathematics and theoretical computer science*. (2026).
-/

open Filter SimpleGraph

namespace Erdos180

variable {V : Type*}

/-- A graph on `Fin n` is `F`-free when it contains no member of the family `F` as a subgraph. -/
def FamilyFree {q : ℕ} (F : Finset (SimpleGraph (Fin q))) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Prop :=
  ∀ H ∈ F, H.Free G

/-- $\mathrm{ex}(n;\mathcal{F})$, the greatest number of edges of a graph on `n` vertices
containing no member of `F`. -/
noncomputable def familyExtremalNumber {q : ℕ} (F : Finset (SimpleGraph (Fin q))) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), FamilyFree F G ∧ G.edgeFinset.card = m}

/--
If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum
number of edges a graph on $n$ vertices can have without containing any subgraphs from
$\mathcal{F}$. Note that it is trivial that $\mathrm{ex}(n;\mathcal{F})\leq \mathrm{ex}(n;G)$ for
every $G\in\mathcal{F}$. Is it true that, for every $\mathcal{F}$, there exists $G\in\mathcal{F}$
such that
$$\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})?$$

This is the Erdős–Simonovits compactness conjecture. The answer is no: OpenAI [OpenAI26] give a
family of connected bipartite graphs, none of them acyclic, for which no single member controls
the family extremal number. See `erdos_180.variants.counterexample`.
-/
@[category research solved, AMS 5]
theorem erdos_180 : answer(False) ↔
    ∀ (q : ℕ) (F : Finset (SimpleGraph (Fin q))), F.Nonempty →
      ∃ H ∈ F, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        (extremalNumber n H : ℝ) ≤ C * (familyExtremalNumber F n : ℝ) := by
  sorry

/--
The counterexample: a nonempty family of connected bipartite graphs, none acyclic, that is not
compact in the sense of `erdos_180`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean"]
theorem erdos_180.variants.counterexample :
    ∃ (q : ℕ) (F : Finset (SimpleGraph (Fin q))),
      F.Nonempty ∧
      (∀ H ∈ F, H.Connected ∧ H.IsBipartite ∧ ¬ H.IsAcyclic) ∧
      ¬ ∃ H ∈ F, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        (extremalNumber n H : ℝ) ≤ C * (familyExtremalNumber F n : ℝ) := by
  sorry

end Erdos180

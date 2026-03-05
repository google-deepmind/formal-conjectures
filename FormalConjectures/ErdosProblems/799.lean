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
# Erdős Problem 799

*Reference:* [erdosproblems.com/799](https://www.erdosproblems.com/799)

Is it true that the list chromatic number $\chi_L(G) = o(n)$ for almost all graphs on $n$ vertices?

[ERT80] Erdős, P., Rubin, A. L. and Taylor, H., *Choosability in graphs*, Proc. West Coast
Conf. on Combinatorics, Graph Theory and Computing, Congressus Numerantium 26 (1980), 125–157.

[Al92] Alon, N., *Choice numbers of graphs: a probabilistic approach*, Combin. Probab.
Comput. 1 (1992), 107–114.

[AKS99] Alon, N., Krivelevich, M. and Sudakov, B., *List coloring of random and
pseudo-random graphs*, Combinatorica 19 (1999), 453–472.
-/

namespace Erdos799

/-- A proper list coloring of $G$ with respect to a list assignment $L : V \to \text{Finset}\ \mathbb{N}$
is a function $f : V \to \mathbb{N}$ such that $f(v) \in L(v)$ for all $v$, and $f(u) \neq f(v)$
whenever $u$ and $v$ are adjacent. -/
def IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph $G$ is $k$-choosable ($k$-list-colorable) if for every list assignment $L$
where each vertex receives a list of at least $k$ colors, there exists a
proper list coloring. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, IsProperListColoring G L f

/-- The simple graph on $\text{Fin}\ n$ determined by a Boolean edge predicate.
Only the upper-triangle entries $ec(\min(u, v), \max(u, v))$ for $u \neq v$ are read. -/
def toGraph {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- The fraction of all labeled graphs on $n$ vertices satisfying property $P$.
Each graph is encoded by a Boolean edge predicate; the graph is read
from the upper triangle, so every graph has equal weight. -/
noncomputable def graphFraction (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  haveI : DecidablePred (fun ec => P (toGraph ec)) := fun _ => Classical.dec _
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter
    (fun ec => P (toGraph ec))).card /
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).card : ℝ)

/--
Erdős Problem 799 [ERT80]:

Is it true that $\chi_L(G) = o(n)$ for almost all graphs on $n$ vertices?

Formally: for every $\varepsilon > 0$ and $\delta > 0$, there exists $n_0$ such that for all
$n \geq n_0$ and all $k \geq \varepsilon n$, the fraction of labeled graphs on $n$ vertices
that are $k$-choosable is at least $1 - \delta$.

The answer is yes. Alon [Al92] proved that the random graph on $n$ vertices with edge
probability $1/2$ has $\chi_L(G) \ll (\log \log n / \log n) \cdot n$ almost surely. Alon,
Krivelevich, and Sudakov [AKS99] improved this to $\chi_L(G) \asymp n / \log n$ almost surely.
-/
@[category research solved, AMS 5]
theorem erdos_799 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, (k : ℝ) ≥ ε * (n : ℝ) →
        graphFraction n (fun G => IsChoosable G k) ≥ 1 - δ := by
  sorry

end Erdos799

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
# Erdős Problem 745

*Reference:* [erdosproblems.com/745](https://www.erdosproblems.com/745)

Describe the size of the second largest component of the random graph on $n$
vertices, where each edge is included independently with probability $1/n$.

Erdős believed that almost surely the second largest component has size
$\ll \log n$. This is true, as proved by Komlós, Sulyok, and Szemerédi.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to
see solved_. Combinatorica 1 (1981), 25-42.

[KSS80] Komlós, J., Sulyok, M., and Szemerédi, E., _Linear problems in
combinatorial number theory_. Acta Math. Acad. Sci. Hungar. 36 (1980), 341-365.
-/

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

namespace Erdos745

/-- The simple graph on `Fin n` determined by a Boolean edge configuration. -/
def toGraph745 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := fun v ⟨h, _⟩ => h rfl

/-- The number of edges in a Boolean edge configuration on `Fin n`
(counting only pairs $i < j$ to avoid double-counting). -/
def edgeCount745 {n : ℕ} (ec : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ ec p.1 p.2 = true)).card

/-- The probability weight of a specific edge configuration under the
Erdős–Rényi model $G(n, 1/n)$: each edge is included independently
with probability $1/n$. -/
noncomputable def gnpWeight745 (n : ℕ) (ec : Fin n → Fin n → Bool) : ℝ :=
  (1 / (n : ℝ)) ^ edgeCount745 ec *
  (1 - 1 / (n : ℝ)) ^ (n.choose 2 - edgeCount745 ec)

/-- The $G(n, 1/n)$-probability of a graph property $P$: the sum of weights
over all edge configurations whose graph satisfies $P$. -/
noncomputable def gnpProb745 (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Finset.univ.filter (fun ec : Fin n → Fin n → Bool =>
    P (toGraph745 ec))).sum (gnpWeight745 n)

/-- The size of the connected component containing vertex $v$ in graph $G$. -/
noncomputable def componentSize745 {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => G.Reachable v w)).card

/-- The size of the second largest connected component of $G$ on `Fin n`.
Defined as the smallest $k$ such that at most one connected component
has more than $k$ vertices; equivalently, any two vertices whose
components both exceed size $k$ must be in the same component. -/
noncomputable def secondLargestComponent745 {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∀ u v : Fin n,
    componentSize745 G u > k → componentSize745 G v > k → G.Reachable u v}

/--
Erdős Problem 745 [Er81]:

In the Erdős–Rényi random graph $G(n, 1/n)$, the second largest connected
component almost surely has size $O(\log n)$.

Formally: there exists a constant $C > 0$ such that for every $\varepsilon > 0$
there exists $n_0$ such that for all $n \geq n_0$, the $G(n, 1/n)$-probability
that the second largest component has size at most $C \cdot \log n$ is at least
$1 - \varepsilon$.

Proved by Komlós, Sulyok, and Szemerédi [KSS80].
-/
@[category research solved, AMS 5 60]
theorem erdos_745 :
    ∃ C : ℝ, C > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      gnpProb745 n (fun G =>
        (secondLargestComponent745 G : ℝ) ≤ C * Real.log (n : ℝ)) ≥ 1 - ε := by
  sorry

end Erdos745

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
# Erdős Problem 572

*Reference:* [erdosproblems.com/572](https://www.erdosproblems.com/572)

Show that for $k \geq 3$,
$$\mathrm{ex}(n; C_{2k}) \gg n^{1 + 1/k}.$$

Here $\mathrm{ex}(n; C_{2k})$ is the Turán extremal number: the maximum number of edges in
an $n$-vertex graph that does not contain the even cycle $C_{2k}$ as a subgraph.

The notation $\gg$ means there exists a positive constant $c > 0$ such that
$\mathrm{ex}(n; C_{2k}) \geq c \cdot n^{1+1/k}$ for all sufficiently large $n$.

A problem of Erdős [Er64c]. The upper bound $\mathrm{ex}(n; C_{2k}) \ll k \cdot n^{1+1/k}$
was proved by Erdős [Er64c] and Bondy–Simonovits [BoSi74]. The matching lower
bound is known for $k = 2$ (Erdős–Klein [Er38]), $k = 3, 5$ (Benson [Be66]),
and $k = 4$ (Wenger). The general case remains open.

[Er64c] Erdős, P., _On extremal problems of graphs and generalized graphs_.
Israel J. Math. 2 (1964), 183–190.

[BoSi74] Bondy, J.A. and Simonovits, M., _Cycles of even length in graphs_.
J. Combin. Theory Ser. B 16 (1974), 97–105.

[Er38] Erdős, P., _On sequences of integers no one of which divides the product
of two others and on some related problems_. Mitt. Forsch.-Inst. Math. Mech.
Univ. Tomsk 2 (1938), 74–82.

[Be66] Benson, C.T., _Minimal regular graphs of girths eight and twelve_.
Canad. J. Math. 18 (1966), 1091–1094.

[LUW95] Lazebnik, F., Ustimenko, V.A., Woldar, A.J., _A new series of dense graphs
of high girth_. Bull. Amer. Math. Soc. (N.S.) 32 (1995), 73–79.

[LUW99] Lazebnik, F., Ustimenko, V.A., Woldar, A.J., _Polarities and 2k-cycle-free
graphs_. Discrete Math. 197/198 (1999), 503–513.
-/

open SimpleGraph

namespace Erdos572

/-- The cycle graph $C_m$ on $m$ vertices ($m \geq 3$). Vertex $i$ is adjacent to vertex
$i + 1 \pmod{m}$ and vertex $i - 1 \pmod{m}$. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- A graph $G$ contains $H$ as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number $\mathrm{ex}(n; H)$: the maximum number of edges in a
simple graph on $n$ vertices that does not contain $H$ as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem 572 [Er64c]:

For every $k \geq 3$, there exists a constant $c > 0$ such that for all sufficiently
large $n$,
$$\mathrm{ex}(n; C_{2k}) \geq c \cdot n^{1 + 1/k}.$$
-/
@[category research open, AMS 5]
theorem erdos_572 (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (extremalNumber (cycleGraph (2 * k) (by omega)) n : ℝ) := by
  sorry

/--
Erdős Problem 572, solved case $k = 2$ (Erdős–Klein [Er38]):

There exists a constant $c > 0$ such that for all sufficiently large $n$,
$\mathrm{ex}(n; C_4) \geq c \cdot n^{3/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_572_k2 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (2 : ℝ)) ≤ (extremalNumber (cycleGraph 4 (by omega)) n : ℝ) := by
  sorry

/--
Erdős Problem 572, solved case $k = 3$ (Benson [Be66]):

There exists a constant $c > 0$ such that for all sufficiently large $n$,
$\mathrm{ex}(n; C_6) \geq c \cdot n^{4/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_572_k3 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤ (extremalNumber (cycleGraph 6 (by omega)) n : ℝ) := by
  sorry

/--
Erdős Problem 572, solved case $k = 4$ (Wenger):

There exists a constant $c > 0$ such that for all sufficiently large $n$,
$\mathrm{ex}(n; C_8) \geq c \cdot n^{5/4}$.
-/
@[category research solved, AMS 5]
theorem erdos_572_k4 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (4 : ℝ)) ≤ (extremalNumber (cycleGraph 8 (by omega)) n : ℝ) := by
  sorry

/--
Erdős Problem 572, solved case $k = 5$ (Benson [Be66]):

There exists a constant $c > 0$ such that for all sufficiently large $n$,
$\mathrm{ex}(n; C_{10}) \geq c \cdot n^{6/5}$.
-/
@[category research solved, AMS 5]
theorem erdos_572_k5 :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (5 : ℝ)) ≤ (extremalNumber (cycleGraph 10 (by omega)) n : ℝ) := by
  sorry

end Erdos572

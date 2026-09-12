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
# Erdős Problem 1021

*References:*
- [erdosproblems.com/1021](https://www.erdosproblems.com/1021)
- [BoSi74] Bondy, J. A. and Simonovits, M., *Cycles of even length in graphs*.
  J. Combinatorial Theory Ser. B (1974), 97-105.
- [CoLe21] Conlon, David and Lee, Joonkyung, *On the extremal number of subdivisions*.
  Int. Math. Res. Not. IMRN (2021), 9122--9145.
- [Er64c] Erdős, P., *Extremal problems in graph theory*. Theory of Graphs and its
  Applications (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Ja19] Janzer, Oliver, *Improved bounds for the extremal number of subdivisions*.
  Electron. J. Combin. (2019), Paper No. 3.3, 6.
-/

open Filter SimpleGraph

namespace Erdos1021

/--
Vertices of $G_k$: $k$ original vertices together with one subdivision vertex for each
unordered pair.
-/
abbrev Vertex (k : ℕ) := Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}

/--
Adjacency of $G_k$ before `SimpleGraph.fromRel` packages it as a graph.

Each subdivision vertex corresponding to a pair $\{i,j\}$ is joined to exactly the two
original endpoints $i$ and $j$. The relation is already symmetric and irreflexive.
-/
def GAdj (k : ℕ) : Vertex k → Vertex k → Prop
  | .inl y, .inr ⟨⟨i, j⟩, _⟩ => y = i ∨ y = j
  | .inr ⟨⟨i, j⟩, _⟩, .inl y => y = i ∨ y = j
  | _, _ => False

/--
The bipartite graph $G_k$ between $\{y_1,\ldots,y_k\}$ and
$\{z_1,\ldots,z_{\binom{k}{2}}\}$, with each $z_j$ joined to a unique pair of $y_i$.

This is the $1$-subdivision of $K_k$.
-/
def G (k : ℕ) : SimpleGraph (Vertex k) :=
  .fromRel (GAdj k)

/-- Each subdivision vertex is joined to both of its original endpoints. -/
@[category test, AMS 5]
theorem G_adj_endpoints {k : ℕ} {i j : Fin k} (hij : i < j) :
    (G k).Adj (.inl i) (.inr ⟨(i, j), hij⟩) ∧
      (G k).Adj (.inl j) (.inr ⟨(i, j), hij⟩) := by
  constructor
  · exact ⟨Sum.inl_ne_inr, Or.inl (Or.inl rfl)⟩
  · exact ⟨Sum.inl_ne_inr, Or.inl (Or.inr rfl)⟩

/-- There are no edges within either part of $G_k$. -/
@[category test, AMS 5]
theorem G_not_adj_within_parts {k : ℕ} (a b : Fin k)
    (p q : {p : Fin k × Fin k // p.1 < p.2}) :
    ¬ (G k).Adj (.inl a) (.inl b) ∧ ¬ (G k).Adj (.inr p) (.inr q) := by
  constructor
  · rintro ⟨_, h | h⟩ <;> exact h.elim
  · rintro ⟨_, h | h⟩ <;> exact h.elim

/--
Is it true that, for every $k\geq 3$, there is a constant $c_k>0$ such that
$$\mathrm{ex}(n,G_k) \ll n^{3/2-c_k},$$
where $G_k$ is the bipartite graph between $\{y_1,\ldots,y_k\}$ and
$\{z_1,\ldots,z_{\binom{k}{2}}\}$, with each $z_j$ joined to a unique pair of $y_i$?

A conjecture of Erdős and Simonovits [Er71], proved by Conlon and Lee [CoLe21] with
$c_k=6^{-k}$, and improved to $c_k=\frac{1}{4k-6}$ by Janzer [Ja19]. When $k=3$ the graph
$G_3$ is the $6$-cycle $C_6$.
-/
@[category research solved, AMS 5]
theorem erdos_1021 : answer(True) ↔
    ∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      Asymptotics.IsBigO atTop
        (fun n : ℕ => (extremalNumber n (G k) : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2 - c)) := by
  sorry

/--
Erdős [Er71] could not even prove whether $\mathrm{ex}(n,G_k)=o(n^{3/2})$. This weaker
bound follows from the power-saving of Conlon–Lee and of Janzer.
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.little_o (k : ℕ) (hk : 3 ≤ k) :
    Asymptotics.IsLittleO atTop
      (fun n : ℕ => (extremalNumber n (G k) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Conlon and Lee [CoLe21] proved the conjecture with $c_k=6^{-k}$, i.e.
$$\mathrm{ex}(n,G_k) \ll n^{3/2-6^{-k}}.$$
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.conlon_lee (k : ℕ) (hk : 3 ≤ k) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (extremalNumber n (G k) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2 - ((6 : ℝ) ^ k)⁻¹)) := by
  sorry

/--
Janzer [Ja19] improved the saving to $c_k=\frac{1}{4k-6}$, i.e.
$$\mathrm{ex}(n,G_k) \ll n^{3/2-\frac{1}{4k-6}}.$$
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.janzer (k : ℕ) (hk : 3 ≤ k) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (extremalNumber n (G k) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  sorry

/--
Erdős and Simonovits proved (in unpublished work) that in any such result one must have
$c_k\to 0$ as $k\to \infty$: no fixed positive saving works for all large $k$.
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.saving_tends_to_zero :
    ∀ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ¬ Asymptotics.IsBigO atTop
          (fun n : ℕ => (extremalNumber n (G k) : ℝ))
          (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2 - c)) := by
  sorry

end Erdos1021

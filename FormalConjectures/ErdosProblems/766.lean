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
# Erdős Problem 766

*References:*
- [erdosproblems.com/766](https://www.erdosproblems.com/766)
- [Er64c] Erdős, P., *Extremal problems in graph theory*. Theory of Graphs and its Applications
  (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
  [PDF](https://www.renyi.hu/~p_erdos/1964-06.pdf)
-/

@[expose] public section

open Filter
open scoped SimpleGraph

namespace Erdos766

/-- $f(n;k,l)$ in the sense of [Er64c], where it is called $f_1(n;k,l)$: the least $m$ such that
every graph with $n$ vertices and $m$ edges contains at least one graph with $k$ vertices and
$l$ edges as a (not necessarily induced) subgraph. There is no graph with $n$ vertices and more
than $\binom{n}{2}$ edges, so the set is nonempty. -/
noncomputable def forcingNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G}

/-- If every graph with $n$ vertices and $m$ edges contains a graph with $k$ vertices and $l$
edges, then $f(n;k,l) \leq m$. -/
@[category API, AMS 5]
theorem forcingNumber_le {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) : forcingNumber n k l ≤ m :=
  Nat.sInf_le h

/-- For $k \leq n$ every graph on $n$ vertices contains the empty graph on $k$ vertices, so
$f(n;k,0) = 0$. -/
@[category test, AMS 5]
theorem forcingNumber_zero {n k : ℕ} (hkn : k ≤ n) : forcingNumber n k 0 = 0 :=
  Nat.eq_zero_of_le_zero <| forcingNumber_le fun _ _ ↦
    ⟨⊥, by simp, SimpleGraph.bot_isContained_iff_card_le.2 (by simpa using hkn)⟩

/-- $f(n;k,l) \leq \mathrm{ex}(n;G) + 1$ for every graph $G$ with $k$ vertices and $l$ edges,
since a graph with more than $\mathrm{ex}(n;G)$ edges contains $G$. Here $\mathrm{ex}(n;G)$ is
`SimpleGraph.extremalNumber n G`, the maximum number of edges of a graph on $n$ vertices with no
copy of $G$. -/
@[category test, AMS 5]
theorem forcingNumber_le_extremalNumber_add_one (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k))
    (h : G.edgeSet.ncard = l) : forcingNumber n k l ≤ SimpleGraph.extremalNumber n G + 1 := by
  classical
  refine forcingNumber_le fun G' hG' ↦ ⟨G, h, ?_⟩
  refine SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset ?_
  rw [Fintype.card_fin, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hG']
  exact Nat.lt_succ_self _

/-- The function of erdosproblems.com: the minimum of $\mathrm{ex}(n;G)$ over all graphs $G$ with
$k$ vertices and $l$ edges. In [Er64c] the least $m$ such that every graph with $n$ vertices and
$m$ edges contains one fixed graph with $k$ vertices and $l$ edges is called $f_2(n;k,l)$, so
this is $f_2(n;k,l) - 1$. The value is in `ℕ∞` and is `⊤` when no such graph $G$ exists. -/
noncomputable def minExtremalNumber (n k l : ℕ) : ℕ∞ :=
  ⨅ (G : SimpleGraph (Fin k)) (_ : G.edgeSet.ncard = l), (SimpleGraph.extremalNumber n G : ℕ∞)

/-- The minimum is at most $\mathrm{ex}(n;G)$ for every graph $G$ with $k$ vertices and $l$
edges. -/
@[category API, AMS 5]
theorem minExtremalNumber_le (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k))
    (h : G.edgeSet.ncard = l) : minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G :=
  iInf₂_le G h

/-- There is no graph with $0$ vertices and $1$ edge, so the minimum is `⊤`. -/
@[category test, AMS 5]
theorem minExtremalNumber_zero_one (n : ℕ) : minExtremalNumber n 0 1 = ⊤ := by
  simp [minExtremalNumber, Set.eq_empty_of_isEmpty]

def erdos_766.parts.i.answer : ℕ → ℕ → ℕ → ℝ := sorry

/--
Let $f(n;k,l)=\min \mathrm{ex}(n;G)$, where $G$ ranges over all graphs with $k$ vertices and $l$
edges.

Give good estimates for $f(n;k,l)$ in the range $k<l\leq k^2/4$.

In [Er64c, p. 33] this question is asked for $f_1(n;k,l)$ (`Erdos766.forcingNumber`), which
forces at least one graph with $k$ vertices and $l$ edges rather than one fixed graph; we follow
the source. The question for the function of erdosproblems.com is
`Erdos766.erdos_766.variants.minExtremalNumber_estimate`.
-/
@[category research open, question value, AMS 5]
theorem erdos_766.parts.i :
    ∀ k l : ℕ, k < l → l ≤ k ^ 2 / 4 →
      (fun n ↦ (forcingNumber n k l : ℝ)) =Θ[atTop] erdos_766.parts.i.answer k l := by
  sorry

/--
For fixed $k$ and large $n$ is $f(n;k,l)$ a strictly monotone function of $l$?

As in `Erdos766.erdos_766.parts.i`, $f$ is $f_1$ of [Er64c], and we use the range
$k<l\leq k^2/4$ in which the question is asked there; here `k ^ 2 / 4` is $\lfloor k^2/4\rfloor$.
The question for the function of erdosproblems.com is
`Erdos766.erdos_766.variants.minExtremalNumber_strictMonoOn`.
-/
@[category research open, question, AMS 5]
theorem erdos_766.parts.ii :
    ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      StrictMonoOn (forcingNumber n k) (Set.Ioc k (k ^ 2 / 4)) := by
  sorry

/--
Dirac and Erdős proved independently that when $l=\lfloor k^2/4\rfloor+1$
$$f(n;k,l)\leq \lfloor n^2/4\rfloor+1.$$

[Er64c, p. 34] states this for every $k \leq n$. We assume $k \geq 3$, since for $k \leq 2$ there
is no graph with $k$ vertices and $\lfloor k^2/4\rfloor+1$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_766.variants.dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  sorry

def erdos_766.variants.minExtremalNumber_estimate.answer : ℕ → ℕ → ℕ → ℝ := sorry

/--
The estimate question of `Erdos766.erdos_766.parts.i` for the function
$\min \mathrm{ex}(n;G)$ of erdosproblems.com (`Erdos766.minExtremalNumber`).
-/
@[category research open, question value, AMS 5]
theorem erdos_766.variants.minExtremalNumber_estimate :
    ∀ k l : ℕ, k < l → l ≤ k ^ 2 / 4 →
      (fun n ↦ ((minExtremalNumber n k l).toNat : ℝ)) =Θ[atTop]
        erdos_766.variants.minExtremalNumber_estimate.answer k l := by
  sorry

/--
The monotonicity question of `Erdos766.erdos_766.parts.ii` for the function
$\min \mathrm{ex}(n;G)$ of erdosproblems.com (`Erdos766.minExtremalNumber`).
-/
@[category research open, question, AMS 5]
theorem erdos_766.variants.minExtremalNumber_strictMonoOn :
    ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      StrictMonoOn (minExtremalNumber n k) (Set.Ioc k (k ^ 2 / 4)) := by
  sorry

end Erdos766

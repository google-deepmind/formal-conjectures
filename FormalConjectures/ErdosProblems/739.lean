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
# Erdős Problem 739

*References:*
- [erdosproblems.com/739](https://www.erdosproblems.com/739)
- [dBE51] de Bruijn, N. G. and Erdős, P., *A colour problem for infinite graphs and a problem in
  the theory of relations*. Indag. Math. (1951), 369-373.
- [Ga73] Galvin, F., *Chromatic numbers of subgraphs*. Period. Math. Hungar. (1973), 117-119.
- [Ko88b] Komjáth, Péter, *Consistency results on infinite graphs*. Israel J. Math. (1988),
  285-294.
- [Sh90] Shelah, Saharon, *Incompactness for chromatic numbers of graphs*. A tribute to Paul Erdős
  (1990), 361-371.
-/

@[expose] public section

open Cardinal SimpleGraph

universe u

namespace Erdos739

/--
Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number $\mathfrak{m}$.
Is it true that, for every infinite cardinal $\mathfrak{n}< \mathfrak{m}$, there exists a subgraph
of $G$ with chromatic number $\mathfrak{n}$?

A question of Galvin [Ga73]. Komjáth [Ko88b] proved it is consistent that
$2^{\aleph_0}=2^{\aleph_1}=2^{\aleph_2}=\aleph_3$ and that there exist graphs which fail this
property (with $\mathfrak{m}=\aleph_2$ and $\mathfrak{n}=\aleph_1$), so the statement below is
not provable in ZFC (if ZFC is consistent). Shelah [Sh90] proved that, assuming the axiom of
constructibility, the answer is yes with $\mathfrak{m}=\aleph_2$ and $\mathfrak{n}=\aleph_1$. It
remains open whether the answer is yes assuming the Generalized Continuum Hypothesis (see
`erdos_739.variants.gch`), so the statement is not known to be refutable either. Consistency
results about models of ZFC are not directly formalizable inside Lean's fixed model, so only the
question is recorded here.

The subgraph need not be induced (see `erdos_739.variants.induced`). The hypothesis that
$\mathfrak{m}$ is infinite follows from $\aleph_0 \le \mathfrak{n} < \mathfrak{m}$.
-/
@[category research open, question, AMS 5]
theorem erdos_739 :
    ∀ (V : Type u) (G : SimpleGraph V) (n : Cardinal.{u}),
      ℵ₀ ≤ n → n < G.chromaticCardinal →
        ∃ H : G.Subgraph, H.coe.chromaticCardinal = n := by
  sorry

/--
Every graph with chromatic number $\mathfrak{m}>\aleph_0$ has a subgraph with chromatic number
$\aleph_0$. This is the case $\mathfrak{n}=\aleph_0$ of the question and follows from the
de Bruijn–Erdős theorem [dBE51]. The source credits Galvin [Ga73] with the case
$\mathfrak{m}=\aleph_0$, which has no infinite $\mathfrak{n}<\mathfrak{m}$; it is read here as
$\mathfrak{n}=\aleph_0$.
-/
@[category research solved, AMS 5]
theorem erdos_739.variants.aleph_zero :
    ∀ (V : Type u) (G : SimpleGraph V), ℵ₀ < G.chromaticCardinal →
      ∃ H : G.Subgraph, H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/--
Galvin [Ga73] proved that the stronger version of `erdos_739`, in which the subgraph is induced,
implies $2^{\mathfrak{k}}<2^{\mathfrak{n}}$ for all cardinals $\mathfrak{k}<\mathfrak{n}$.
-/
@[category research solved, AMS 3 5]
theorem erdos_739.variants.induced :
    (∀ (V : Type u) (G : SimpleGraph V) (n : Cardinal.{u}),
      ℵ₀ ≤ n → n < G.chromaticCardinal →
        ∃ s : Set V, (G.induce s).chromaticCardinal = n) →
    ∀ κ μ : Cardinal.{u}, κ < μ → (2 : Cardinal.{u}) ^ κ < 2 ^ μ := by
  sorry

/--
It remains open whether the answer to `erdos_739` is yes assuming the Generalized Continuum
Hypothesis, stated as $2^{\mathfrak{c}} = \mathfrak{c}^+$ for every infinite cardinal
$\mathfrak{c}$.
-/
@[category research open, question, AMS 3 5]
theorem erdos_739.variants.gch :
    (∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c) →
    ∀ (V : Type u) (G : SimpleGraph V) (n : Cardinal.{u}),
      ℵ₀ ≤ n → n < G.chromaticCardinal →
        ∃ H : G.Subgraph, H.coe.chromaticCardinal = n := by
  sorry

end Erdos739

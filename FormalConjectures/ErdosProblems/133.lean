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
# Erdős Problem 133

*References:*
- [erdosproblems.com/133](https://www.erdosproblems.com/133)
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [HaSe84] Hanson, D. and Seyffarth, K., *$k$-saturated graphs of prescribed maximum degree*.
  Congr. Numer. (1984), 169-182.
- [FuSe94] Füredi, Zoltán and Seress, Ákos, *Maximal triangle-free graphs with restrictions on the
  degrees*. J. Graph Theory (1994), 11-24.
- [HaLe18] Haviv, Ishay and Levy, Dan, *Symmetric complete sum-free sets in cyclic groups*. Israel
  J. Math. (2018), 931-956.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos133

open scoped Classical in
/--
`f n` is the least possible maximum degree of a triangle-free graph on `n` vertices with
diameter `2`, i.e. the largest `f` such that every such graph has a vertex of degree `≥ f`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧ ∀ v, G.degree v ≤ d}

/--
Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices and diameter
$2$ contains a vertex with degree $\geq f(n)$. What is the order of growth of $f(n)$? Does
$f(n)/\sqrt{n}\to \infty$?

Asked by Erdős and Pach. The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that
a graph with maximum degree $d$ and diameter $2$ has at most $1+d+d(d-1)=d^2+1$ many vertices.

Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$ using a Cayley graph
on $\mathbb{Z}/n\mathbb{Z}$, with the generating set given by some symmetric complete sum-free set
of size $\sim \sqrt{n}$. An alternative construction of such a complete sum-free set was given by
Haviv and Levy [HaLe18]. Füredi and Seress [FuSe94] proved that
$f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. In particular $f(n)/\sqrt{n}\not\to\infty$.

The precise asymptotics of $f(n)$ are unknown; Alon believes that the truth is $f(n)\sim \sqrt{n}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean#L597"]
theorem erdos_133 : answer(False) ↔ Tendsto (fun n : ℕ ↦ (f n : ℝ) / √n) atTop atTop := by
  sorry

/-- The order of growth of $f(n)$ is $\sqrt{n}$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean#L597"]
theorem erdos_133.variants.isTheta : (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

/--
The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that a graph with maximum degree
$d$ and diameter $2$ has at most $d^2+1$ many vertices.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.lower_bound : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (1 - ε) * √n ≤ f n := by
  sorry

/-- Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_133.variants.hanson_seyffarth : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (√2 + ε) * √n := by
  sorry

/-- Füredi and Seress [FuSe94] proved that $f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_133.variants.furedi_seress : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (2 / √3 + ε) * √n := by
  sorry

/-- Is $f(n)\sim \sqrt{n}$? Alon believes that this is the truth. -/
@[category research open, AMS 5]
theorem erdos_133.variants.asymptotic :
    answer(sorry) ↔ (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] fun n ↦ √n := by
  sorry

end Erdos133

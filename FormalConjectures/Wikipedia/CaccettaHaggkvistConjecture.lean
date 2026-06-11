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
# Caccetta–Häggkvist conjecture

The Caccetta–Häggkvist conjecture (1978) states that every simple digraph on $n$ vertices
in which every vertex has out-degree at least $n/r$ contains a directed cycle of length
at most $r$.

The most famous special case is $r = 3$: every simple digraph on $n$ vertices with minimum
out-degree at least $n/3$ should contain a directed cycle of length at most $3$. This case
is open; the best known partial results replace $n/3$ by $cn$ for constants $c > 1/3$,
e.g. $c = 3 - \sqrt{7} \approx 0.3542$ (Shen).

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Caccetta%E2%80%93H%C3%A4ggkvist_conjecture)

*References:*
* [CaHa78] Caccetta, L. and Häggkvist, R. (1978). "On minimal digraphs with given girth."
  *Congressus Numerantium* XXI, pp. 181--187.
* [ChSz83] Chvátal, V. and Szemerédi, E. (1983). "Short cycles in directed graphs."
  *J. Combin. Theory Ser. B* 35, pp. 323--327.
* [Sh98] Shen, J. (1998). "Directed triangles in digraphs."
  *J. Combin. Theory Ser. B* 74, pp. 405--407.
* [Su06] Sullivan, B. D. (2006). "A summary of results and problems related to the
  Caccetta-Häggkvist conjecture." [arXiv:math/0605646](https://arxiv.org/abs/math/0605646)
-/

namespace CaccettaHaggkvist

variable {V : Type*}

/--
The out-degree of a vertex `v` in a digraph `G` on a finite vertex type: the number of
vertices `w` with an arc `v → w`.
-/
def outDegree [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter fun w => G.Adj v w).card

/--
`HasDirectedCycleOfLength G k` says that the digraph `G` contains a directed cycle of
length `k`, encoded as an injective map $f : \mathbb{Z}/k\mathbb{Z} \to V$ such that
$f(i) \to f(i+1)$ is an arc of `G` for every $i$. The cyclic index type provides the
wraparound arc $f(k-1) \to f(0)$, and injectivity ensures the cycle visits `k` distinct
vertices. This is only meaningful for `k ≠ 0`. For `k = 1` it asks for a loop
$f(0) \to f(0)$, which is impossible in a loopless (irreflexive) digraph.
-/
def HasDirectedCycleOfLength (G : Digraph V) (k : ℕ) : Prop :=
  ∃ f : ZMod k → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1))

/--
**The Caccetta–Häggkvist conjecture** [CaHa78].

Every simple digraph on $n \ge 1$ vertices in which every vertex has out-degree at least
$n/r$ contains a directed cycle of length at most $r$.

Conventions:
* The hypothesis `n ≤ r * outDegree G v` is the integer form of
  $\operatorname{outdeg}(v) \ge n/r$, avoiding rational division.
* "Simple digraph" here means a digraph without loops (`Irreflexive G.Adj`); pairs of
  opposite arcs (digons, i.e. $2$-cycles $u \to v \to u$) are allowed, as in the standard
  statement of the conjecture. Since a digon is a directed cycle of length $2 \le r$,
  the content of the conjecture lies in digon-free digraphs and $r \ge 3$.
* The hypothesis `1 ≤ n` excludes the empty digraph, for which the degree hypothesis is
  vacuous but no directed cycle exists.
-/
@[category research open, AMS 5]
theorem caccetta_haggkvist (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (V : Type) [Fintype V]
    (hV : Fintype.card V = n) (G : Digraph V) [DecidableRel G.Adj]
    (hirr : Irreflexive G.Adj)
    (hdeg : ∀ v, n ≤ r * outDegree G v) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ HasDirectedCycleOfLength G k := by
  sorry

namespace variants

/--
**The triangle case ($r = 3$) of the Caccetta–Häggkvist conjecture.**

Every simple digraph on $n \ge 1$ vertices with minimum out-degree at least $n/3$
contains a directed cycle of length at most $3$. This is the most studied special case of
the conjecture and is open; Chvátal and Szemerédi [ChSz83] proved the conclusion under the
stronger hypothesis $\operatorname{outdeg}(v) \ge (3 - \sqrt{5})n/2 \approx 0.382\, n$,
and Shen [Sh98] under $\operatorname{outdeg}(v) \ge (3 - \sqrt{7})\, n \approx 0.3542\, n$.
-/
@[category research open, AMS 5]
theorem caccetta_haggkvist_triangle (n : ℕ) (hn : 1 ≤ n) (V : Type) [Fintype V]
    (hV : Fintype.card V = n) (G : Digraph V) [DecidableRel G.Adj]
    (hirr : Irreflexive G.Adj)
    (hdeg : ∀ v, n ≤ 3 * outDegree G v) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  sorry

end variants

/--
Sanity check for the cycle encoding: the complete loopless digraph on three vertices
(arcs $x \to y$ for all $x \ne y$) contains a directed cycle of length $3$.
-/
@[category test, AMS 5]
theorem complete_digraph_three_hasDirectedCycleOfLength_three :
    HasDirectedCycleOfLength (Digraph.mk' fun x y : Fin 3 => x != y) 3 := by
  unfold HasDirectedCycleOfLength
  decide

/--
Sanity check for the out-degree definition: in the complete loopless digraph on three
vertices, every vertex has out-degree $2$, so the degree hypothesis of the triangle case
($n \le 3 \cdot \operatorname{outdeg}(v)$ with $n = 3$) is satisfied.
-/
@[category test, AMS 5]
theorem complete_digraph_three_outDegree (v : Fin 3) :
    outDegree (Digraph.mk' fun x y : Fin 3 => x != y) v = 2 := by
  unfold outDegree
  revert v
  decide

end CaccettaHaggkvist

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
# Erdős Problem 78

*References:*
- [erdosproblems.com/78](https://www.erdosproblems.com/78)
- [Co15] Cohen, Gil, *Two-source dispersers for polylogarithmic entropy and improved Ramsey
  graphs*. arXiv:1506.04428 (2015).
- [Er47] Erdős, P., *Some remarks on the theory of graphs*. Bull. Amer. Math. Soc. (1947),
  292-294.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er88] Erdős, P, Problems and results in combinatorial analysis and graph theory. Discrete Math.
  (1988), 81-92.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory. Quaestiones
  Math. (1993), 333-350.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Li23b] Li, Xin, *Two source extractors for asymptotically optimal entropy, and (many) more*.
  arXiv:2303.06802 (2023).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter Real ComplexityTheory

namespace Erdos78

/--
The graph on `Fin n` described by an adjacency oracle `adj`. Two distinct vertices `u` and `v`
are adjacent if `adj (1ⁿ, u, v)` or `adj (1ⁿ, v, u)` is `true`.

The number of vertices is given in unary, as the list `List.replicate n true`. So if `adj` is
computable in polynomial time, then the whole graph on `n` vertices is computable in time
polynomial in `n`. This is the usual notion of an *explicit* family of graphs.
-/
def explicitGraph (adj : List Bool × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (List.replicate n true, u, v)

/--
The graph `G` has no clique and no independent set with `m` vertices.
-/
def NoHomogeneousSet {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree m

/--
Let $R(k)$ be the Ramsey number for $K_k$. Give a constructive proof that $R(k) > C^k$ for some
constant $C > 1$.

Equivalently, give an explicit construction of graphs on $n$ vertices which contain no clique
and no independent set of size $\geq c \log n$, for some constant $c > 0$.

We formalise "explicit" as: the adjacency relation of the graph on $n$ vertices is decided by a
single algorithm that runs in time polynomial in $n$ (see `explicitGraph`).

This problem is #4 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5 68]
theorem erdos_78 :
    ∃ c > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈c * log n⌉₊ := by
  sorry

/--
Erdős [Er47] gave a simple probabilistic, non-constructive proof that $R(k) > C^k$ for some
constant $C > 1$. In fact $R(k) > 2^{k/2}$ for all $k \geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_78.variants.nonconstructive :
    ∃ C > (1 : ℝ), ∀ᶠ k in atTop, C ^ k < (SimpleGraph.diagonalRamsey k : ℝ) := by
  sorry

/--
Erdős also asked for an explicit construction of graphs on $n$ vertices whose largest clique and
independent set have size $o(n^{1/2})$. Such constructions are now known; see [Co15] for the
history.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.little_o_sqrt :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ √(n : ℝ)) ∧
      ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
        ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈f n⌉₊ := by
  sorry

/--
Cohen [Co15] constructed explicit graphs on $n$ vertices with no clique and no independent set
of size $2^{(\log \log n)^C}$, for some constant $C > 0$.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.cohen :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop,
        NoHomogeneousSet (explicitGraph adj n) ⌈(2 : ℝ) ^ (log (log n)) ^ C⌉₊ := by
  sorry

/--
Li [Li23b] improved this to explicit graphs on $n$ vertices with no clique and no independent set
of size $(\log n)^C$, for some constant $C > 0$.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.li :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  sorry

end Erdos78

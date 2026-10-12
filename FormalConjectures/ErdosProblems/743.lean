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
# Erdős Problem 743

*References:*
- [erdosproblems.com/743](https://www.erdosproblems.com/743)
- [ABCHPT21] Allen, Peter and Böttcher, Julia and Clemens, Dennis and Hladký, Jan and Piguet,
  Diana and Taraz, Anusch, *The tree packing conjecture for trees of almost linear maximum
  degree*. arXiv:2106.11720 (2021).
- [Bo83] Bollobás, Béla, *Some remarks on packing trees*. Discrete Math. (1983), 203-204.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Fi83] Fishburn, P. C., *Balanced integer arrays: a matrix packing theorem*. J. Combin. Theory
  Ser. A (1983), 98-101.
- [Fi83b] Fishburn, P. C., *Packing graphs with odd and even trees*. J. Graph Theory (1983),
  369-383.
- [GyLe78] Gyárfás, A. and Lehel, J., *Packing trees of different order into $K_n$*.
  Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Colloq. Math. Soc. János Bolyai
  18 (1978), 463-469.
- [JKKO19] Joos, Felix and Kim, Jaehoon and Kühn, Daniela and Osthus, Deryk, *Optimal packings
  of bounded degree trees*. J. Eur. Math. Soc. (JEMS) (2019), 3573-3647.
- [JaMo24] Janzer, Barnabás and Montgomery, Richard, *Packing the largest trees in the tree
  packing conjecture*. arXiv:2403.10515 (2024).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos743

/-- `IsPacking n S T` says that the graphs `T k`, for `k ∈ S`, pack into the complete graph
$K_n$ on `Fin n`.

That is, for each $k \in S$ there is an injective map $f_k : \{0, \ldots, k - 1\} \to
\{0, \ldots, n - 1\}$, such that the graphs `(T k).map (f k)` have pairwise disjoint edge sets.
Every graph on `Fin n` is a subgraph of $K_n$, so this says that $K_n$ contains pairwise
edge-disjoint copies of the graphs `T k`. -/
def IsPacking (n : ℕ) (S : Set ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)) : Prop :=
  ∃ f : (k : S) → Fin k → Fin n, (∀ k : S, Function.Injective (f k)) ∧
    ∀ k l : S, (k : ℕ) < (l : ℕ) →
      Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet

/-- A packing of the graphs indexed by `S` gives a packing of those indexed by a subset `S'`. -/
@[category API, AMS 5]
theorem IsPacking.mono {n : ℕ} {S S' : Set ℕ} {T : (k : ℕ) → SimpleGraph (Fin k)}
    (h : IsPacking n S T) (hS : S' ⊆ S) : IsPacking n S' T := by
  obtain ⟨f, hinj, hdisj⟩ := h
  exact ⟨fun k => f ⟨k, hS k.2⟩, fun k => hinj ⟨k, hS k.2⟩,
    fun k l hkl => hdisj ⟨k, hS k.2⟩ ⟨l, hS l.2⟩ hkl⟩

/-- The numbers of edges $k - 1$ of trees on $k$ vertices, for $2 \leq k \leq n$, add up to the
number $\binom{n}{2}$ of edges of $K_n$. -/
@[category test, AMS 5]
theorem sum_Icc_two_sub_one (n : ℕ) : ∑ k ∈ Finset.Icc 2 n, (k - 1) = n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n
      simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih,
        show (n + 1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ n 1,
        Nat.choose_one_right]
      omega

/--
Let $T_2,\ldots,T_n$ be a collection of trees such that $T_k$ has $k$ vertices. Can we always
write $K_n$ as the edge disjoint union of the $T_k$?

A conjecture of Gyárfás, known as the tree packing conjecture. We state it as a packing. For
every $n$ and all trees $T_k$ on the vertex set `Fin k`, $2 \leq k \leq n$, there are injective
maps
$f_k : \{0, \ldots, k - 1\} \to \{0, \ldots, n - 1\}$ such that the graphs $f_k(T_k)$ are
pairwise edge-disjoint (see `IsPacking`). Every tree with $k$ vertices is isomorphic to a tree
on `Fin k`, so this covers every collection of trees.

A tree with $k$ vertices has $k - 1$ edges, and $\sum_{k=2}^{n} (k - 1) = \binom{n}{2}$ is the
number of edges of $K_n$. Hence the copies $f_k(T_k)$ of a packing cover every edge of $K_n$.
So a packing is the same as a decomposition of $K_n$ into copies of $T_2, \ldots, T_n$.
-/
@[category research open, AMS 5]
theorem erdos_743 : answer(sorry) ↔
    ∀ n : ℕ, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree) → IsPacking n (Set.Icc 2 n) T := by
  sorry

/--
Gyárfás and Lehel [GyLe78] proved that this holds if all but at most $2$ of the trees are stars,
or if all the trees are stars or paths. This variant is the second case: each tree is a star or a
path.

Here a star on `Fin k` is `starGraph c` for a centre `c`, and a path is a graph isomorphic to
`pathGraph k`.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.stars_or_paths (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧
      ((∃ c : Fin k, T k = starGraph c) ∨ Nonempty (T k ≃g pathGraph k))) :
    IsPacking n (Set.Icc 2 n) T := by
  sorry

/--
Gyárfás and Lehel [GyLe78] proved that this holds if all but at most $2$ of the trees are stars,
or if all the trees are stars or paths. This variant is the first case.

Here a star on `Fin k` is `starGraph c` for a centre `c`. The two trees that may fail to be
stars are $T_a$ and $T_b$.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.all_but_two_stars (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree)
    (hstar : ∃ a b : ℕ, ∀ k ∈ Set.Icc 2 n, k ≠ a → k ≠ b → ∃ c : Fin k, T k = starGraph c) :
    IsPacking n (Set.Icc 2 n) T := by
  sorry

/--
Fishburn [Fi83b] proved this for $n\leq 9$.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.fishburn (n : ℕ) (hn : n ≤ 9) (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ Set.Icc 2 n, (T k).IsTree) :
    IsPacking n (Set.Icc 2 n) T := by
  sorry

/--
Bollobás [Bo83] proved that the smallest $\lfloor n/\sqrt{2}\rfloor$ many trees can always be
packed greedily into $K_n$.

The smallest trees are $T_1, \ldots, T_m$ with $m = \lfloor n/\sqrt{2} \rfloor$. The tree $T_1$ is
a single vertex, so we only pack $T_2, \ldots, T_m$.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.bollobas (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k ∈ Set.Icc 2 ⌊(n : ℝ) / Real.sqrt 2⌋₊, (T k).IsTree) :
    IsPacking n (Set.Icc 2 ⌊(n : ℝ) / Real.sqrt 2⌋₊) T := by
  sorry

open scoped Classical in
/--
Joos, Kim, Kühn, and Osthus [JKKO19] proved that this conjecture holds when the trees have
bounded maximum degree. That is, for every $d$ there is $N$ such that for all $n \geq N$ the
following holds. If $T_k$ is a tree with $k$ vertices and maximum degree at most $d$ for
$2 \leq k \leq n$, then $K_n$ decomposes into $T_2, \ldots, T_n$.

They even allow the first $o(n)$ trees to have arbitrary maximum degree.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.bounded_degree (d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ (T k).maxDegree ≤ d) →
        IsPacking n (Set.Icc 2 n) T := by
  sorry

open scoped Classical in
/--
Allen, Böttcher, Clemens, Hladký, Piguet, and Taraz [ABCHPT21] proved that this conjecture holds
when all the trees have maximum degree $\leq c\frac{n}{\log n}$ for some constant $c>0$. That is,
there is $c > 0$ such that for all sufficiently large $n$ the following holds. If $T_k$ is a tree
with $k$ vertices and maximum degree at most $cn/\log n$ for $2 \leq k \leq n$, then $K_n$
decomposes into $T_2, \ldots, T_n$.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.almost_linear_degree :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k ∈ Set.Icc 2 n,
        (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log (n : ℝ)) →
        IsPacking n (Set.Icc 2 n) T := by
  sorry

/--
Janzer and Montgomery [JaMo24] have proved that there exists some $c>0$ such that the largest $cn$
trees can be packed into $K_n$.

We state this for all sufficiently large $n$. The trees are $T_k$ with $n - cn < k \leq n$, and
we also require $2 \leq k$.
-/
@[category research solved, AMS 5]
theorem erdos_743.variants.largest_trees :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
      (∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - c * n < k → (T k).IsTree) →
        IsPacking n {k : ℕ | 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - c * n < k} T := by
  sorry

end Erdos743

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
# Erdős Problem 5

*References:*
- [erdosproblems.com/5](https://www.erdosproblems.com/5)
- [BFM16] Banks, William D. and Freiberg, Tristan and Maynard, James, *On limit points of the
  sequence of normalized prime gaps*. Proc. Lond. Math. Soc. (3) (2016), 515-539.
- [Er55] Erdős, Paul, *Some remarks on number theory*. Riveon Lematematika (1955), 45-48.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Er85c] Erdős, P., *On some of my problems in number theory I would most like to see solved*.
  Number theory (Ootacamund, 1984) (1985), 74-84.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [GPY09] Goldston, Daniel A. and Pintz, János and Yıldırım, Cem Y., *Primes in tuples. I*.
  Ann. of Math. (2) (2009), 819-862.
- [HiMa88] Hildebrand, Adolf and Maier, Helmut, *Gaps between prime numbers*. Proc. Amer. Math.
  Soc. (1988), 1-9.
- [Me20] Merikoski, Jori, *Limit points of normalized prime gaps*. J. Lond. Math. Soc. (2) (2020),
  99-124.
- [Pi16] Pintz, János, *Polignac numbers, conjectures of Erdős on gaps between primes, arithmetic
  progressions in primes, and the bounded gap conjecture*. From arithmetic to zeta-functions
  (2016), 367-384.
- [Ri56] Ricci, Giovanni, *Recherches sur l'allure de la suite $\{p_{n+1}-p_n/\log p_n\}$*.
  Colloque sur la Théorie des Nombres, Bruxelles, 1955 (1956), 93-106.
- [We31] Westzynthius, E., *Über die Verteilung der Zahlen, die zu den n ersten Primzahlen
  teilerfremd sind*. Commentat. Phys. Math. (1931), 1-37.
-/

open Filter MeasureTheory Real Set
open scoped Topology

namespace Erdos5

/--
The normalised prime gap $\frac{p_{n+1}-p_n}{\log n}$, where $p_n$ denotes the $n$-th prime.
-/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / log n

/--
The set $S$ of limit points of $\frac{p_{n+1}-p_n}{\log n}$.

Only the *finite* limit points are collected here; that $\infty$ is also a limit point is
Westzynthius' theorem, recorded separately as `erdos_5.variants.westzynthius`.

Erdős' question, as well as [HiMa88] and [Pi16], normalises the prime gaps by $\log n$, whereas
[GPY09], [BFM16] and [Me20] normalise by $\log p_n$. Since $\log p_n/\log n \to 1$ the two
normalisations have the same limit points, so all the results below are stated for the
normalisation used here.
-/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

/--
Let $C\geq 0$. Is there an infinite sequence of $n_i$ such that
$$\lim_{i\to \infty}\frac{p_{n_i+1}-p_{n_i}}{\log n_i}=C?$$

We formalise "an infinite sequence of $n_i$" as a strictly monotone sequence of indices
`n : ℕ → ℕ`. Note that the numerator is the gap between the two *consecutive* primes
$p_{n_i}$ and $p_{n_i+1}$, which is `primeGap (n i)`, and not the gap between the primes
indexed by two consecutive members of the sequence.
-/
@[category research open, AMS 11]
theorem erdos_5 : answer(sorry) ↔ ∀ C : ℝ, 0 ≤ C →
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C) := by
  sorry

/--
Let $S$ be the set of limit points of $(p_{n+1}-p_n)/\log n$. This problem asks whether
$S=[0,\infty]$.

Since $\infty\in S$ is known (see `erdos_5.variants.westzynthius`), the open content is the
equality of the finite part of $S$ with $[0,\infty)$.
-/
@[category research open, AMS 11]
theorem erdos_5.variants.limit_point_set : answer(sorry) ↔ limitPointSet = Ici 0 := by
  sorry

/--
$\infty\in S$ by Westzynthius' result [We31] on large prime gaps.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.westzynthius :
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop atTop := by
  sorry

/--
$0\in S$ by the work of Goldston, Pintz, and Yildirim [GPY09] on small prime gaps.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.goldston_pintz_yildirim : (0 : ℝ) ∈ limitPointSet := by
  sorry

/--
Erdős [Er55] and Ricci [Ri56] independently showed that $S$ has positive Lebesgue measure.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.erdos_ricci : 0 < volume limitPointSet := by
  sorry

/--
Hildebrand and Maier [HiMa88] showed that $S$ contains arbitrarily large (finite) numbers.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.hildebrand_maier : ∀ C : ℝ, ∃ x ∈ limitPointSet, C < x := by
  sorry

/--
[HiMa88] in fact prove the stronger statement that there is a constant $c>0$ with
$\lambda([0,T]\cap S)\geq cT$ for all sufficiently large $T$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.hildebrand_maier_measure : ∃ c > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
    ENNReal.ofReal (c * T) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/--
Pintz [Pi16] showed that there exists some small constant $c>0$ such that $[0,c]\subset S$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.pintz : ∃ c > (0 : ℝ), Icc 0 c ⊆ limitPointSet := by
  sorry

/--
Banks, Freiberg, and Maynard [BFM16] showed that at least $12.5\%$ of $[0,\infty)$ belongs
to $S$.

This is [BFM16, Theorem 1.1]: for any nine nonnegative reals
$\beta_1\leq\beta_2\leq\cdots\leq\beta_9$, at least one of the differences $\beta_j-\beta_i$
with $i<j$ belongs to $S$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.banks_freiberg_maynard (β : Fin 9 → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hβmono : Monotone β) : ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  sorry

/--
The $12.5\%$ claim itself, as deduced in [BFM16, Corollary 1.2]:
$\lambda([0,T]\cap S)\geq (1-o(1))T/8$ as $T\to\infty$.

Note that the constant $1/8$ is only attained asymptotically and ineffectively; the bound
[BFM16] obtain for *all* $T>0$ is the weaker $\lambda([0,T]\cap S)>T/22$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.banks_freiberg_maynard_measure : ∀ ε > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
    ENNReal.ofReal ((1 - ε) * T / 8) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/--
Merikoski [Me20] showed that at least $1/3$ of $[0,\infty)$ belongs to $S$.

This is [Me20, Theorem 1]: for any reals $\beta_1\leq\beta_2\leq\beta_3\leq\beta_4$, at least
one of the differences $\beta_j-\beta_i$ with $i<j$ belongs to $S$. Note that, in contrast with
`erdos_5.variants.banks_freiberg_maynard`, the $\beta_i$ are not required to be nonnegative.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.merikoski (β : Fin 4 → ℝ) (hβmono : Monotone β) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  sorry

/--
The $1/3$ claim itself [Me20, Corollary 2]: $\lambda([0,T]\cap S)\geq T/3$ for all $T>0$.

Unlike the $1/8$ of [BFM16], this bound holds uniformly in $T$ with no error term.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.merikoski_measure : ∀ T > (0 : ℝ),
    ENNReal.ofReal (T / 3) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/--
Merikoski [Me20] showed that $S$ has bounded gaps.

This is [Me20, Corollary 3]: there is a (ineffective) constant $C\geq 0$ such that
$S\cap[T,T+C]\neq\emptyset$ for all $T\geq 0$.
-/
@[category research solved, AMS 11]
theorem erdos_5.variants.merikoski_bounded_gaps :
    ∃ C ≥ (0 : ℝ), ∀ T ≥ (0 : ℝ), (limitPointSet ∩ Icc T (T + C)).Nonempty := by
  sorry

/--
In [Er65b], [Er85c], and [Er97c] Erdős asks whether $S$ is everywhere dense (but Weisenberg
notes that clearly $S$ is closed so this is equivalent to asking whether $S=[0,\infty]$).
-/
@[category research open, AMS 11]
theorem erdos_5.variants.dense : answer(sorry) ↔ Ici (0 : ℝ) ⊆ closure limitPointSet := by
  sorry

/--
Membership in `limitPointSet` is exactly the existence of an infinite sequence of indices
along which the normalised prime gaps converge, as in the statement of `erdos_5`.
-/
@[category test, AMS 11]
theorem mem_limitPointSet_iff (x : ℝ) : x ∈ limitPointSet ↔
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 x) :=
  ⟨fun hx => hx.tendsto_subseq, fun ⟨_n, hn, h⟩ => h.mapClusterPt.of_comp hn.tendsto_atTop⟩

/-- The normalised prime gaps are nonnegative. -/
@[category test, AMS 11]
theorem normalizedGap_nonneg (n : ℕ) : 0 ≤ normalizedGap n :=
  div_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)

/-- Every limit point of the normalised prime gaps is nonnegative. -/
@[category test, AMS 11]
theorem limitPointSet_subset_Ici : limitPointSet ⊆ Ici 0 := by
  intro x hx
  obtain ⟨n, -, h⟩ := (mem_limitPointSet_iff x).1 hx
  exact ge_of_tendsto' h fun i => normalizedGap_nonneg (n i)

/--
The statement of `erdos_5` is equivalent to the description of the set of limit points in
`erdos_5.variants.limit_point_set`; combine with `mem_limitPointSet_iff` to unfold the
membership into the sequence of indices $n_i$.
-/
@[category test, AMS 11]
theorem erdos_5_iff_limit_point_set :
    (∀ C : ℝ, 0 ≤ C → C ∈ limitPointSet) ↔ limitPointSet = Ici 0 :=
  ⟨fun h => limitPointSet_subset_Ici.antisymm h, fun h _ hC => h ▸ hC⟩

/--
The set $S$ of limit points is closed, as Weisenberg notes in the acknowledgements to
[erdosproblems.com/5](https://www.erdosproblems.com/5); consequently `erdos_5.variants.dense`
and `erdos_5.variants.limit_point_set` ask the same question.
-/
@[category test, AMS 11]
theorem isClosed_limitPointSet : IsClosed limitPointSet := isClosed_setOf_clusterPt

/--
Weisenberg's remark, as reported on [erdosproblems.com/5](https://www.erdosproblems.com/5):
since $S$ is closed, asking that $S$ be everywhere dense in $[0,\infty)$ is the same as asking
that $S=[0,\infty)$, so `erdos_5.variants.dense` and `erdos_5.variants.limit_point_set` pose the
same question.
-/
@[category test, AMS 11]
theorem dense_iff_limit_point_set :
    Ici (0 : ℝ) ⊆ closure limitPointSet ↔ limitPointSet = Ici 0 := by
  rw [isClosed_limitPointSet.closure_eq]
  exact ⟨fun h => limitPointSet_subset_Ici.antisymm h, fun h => h.ge⟩

-- See also Erdős Problem 234, which concerns the density of the integers `n` with
-- `(p (n + 1) - p n) / log n < c`.

end Erdos5

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
# Erdős Problem 1012

*References:*
- [erdosproblems.com/1012](https://www.erdosproblems.com/1012)
- [Bo71b] Bondy, J. A., *Large cycles in graphs*. Discrete Math. (1971/72), 121--132.
- [Er62e] Erdős, P., *Remarks on a paper of Pósa*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1962),
  227--229.
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Or61] Ore, Oystein, *Arc coverings of graphs*. Ann. Mat. Pura Appl. (4) (1961), 315--321.
- [Wo72] Woodall, D. R., *Sufficient conditions for circuits in graphs*. Proc. London Math. Soc.
  (3) (1972), 739--755.
-/

open SimpleGraph

namespace Erdos1012

/--
`ForcesCycle k n` means that every graph on `n` vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $n-k$ vertices.
-/
def ForcesCycle (k n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeSet.ncard →
      cycleGraph (n - k) ⊑ G

/--
$f(k)$ is the least positive $N$ such that every graph on $n\geq N$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $n-k$ vertices.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ ∀ n ≥ N, ForcesCycle k n}

/--
Let $k\geq 0$. Let $f(k)$ be such that every graph on $n\geq f(k)$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $n-k$ vertices. Determine or
estimate $f(k)$.

Woodall [Wo72] proved that every graph on $n\geq 2k+3$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $l$ vertices for all
$3\leq l\leq n-k$. This settles this question completely.
-/
@[category research solved, AMS 5]
theorem erdos_1012 (k : ℕ) : f k ≤ 2 * k + 3 := by
  sorry

/--
Erdős [Er62e] proved that $f(k)$ exists for all $k\geq 0$; this is not immediately stated in
[Er62e], but Cambie has in the comments explained why the existence of $f(k)$ follows from the
result of [Er62e].
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.exists (k : ℕ) : 0 < f k := by
  sorry

/--
Ore [Or61] proved that $f(0)=1$, in other words, every graph on $n\geq 1$ vertices with at least
$\binom{n-1}{2}+2$ edges contains a Hamiltonian cycle on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.ore : f 0 = 1 := by
  sorry

/--
Bondy [Bo71b] proved that $f(1)=1$.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.bondy : f 1 = 1 := by
  sorry

/--
Woodall [Wo72] proved that every graph on $n\geq 2k+3$ vertices with at least
$\binom{n-k-1}{2}+\binom{k+2}{2}+1$ edges contains a cycle on $l$ vertices for all
$3\leq l\leq n-k$.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.woodall (k n : ℕ) (G : SimpleGraph (Fin n))
    (hn : 2 * k + 3 ≤ n)
    (he : (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeSet.ncard) :
    ∀ l, 3 ≤ l → l ≤ n - k → cycleGraph l ⊑ G := by
  sorry

end Erdos1012

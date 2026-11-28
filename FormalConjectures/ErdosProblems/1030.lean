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
# Erdős Problem 1030

*References:*
- [erdosproblems.com/1030](https://www.erdosproblems.com/1030)
- [BEFS89] Burr, S. and Erdős, P. and Faudree, R. J. and Schelp, R. H., On the difference between
  consecutive Ramsey numbers. Utilitas Math. (1989), 115-118.
- [Er81] Erdős, P., Some new problems and results in graph theory and other branches of
  combinatorial mathematics. Combinatorics and graph theory (Calcutta, 1980), Lecture Notes in
  Math. 885 (1981), 9-17.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory.
  Quaestiones Math. 16 (1993), 333-350.
-/

@[expose] public section

open Filter

namespace Erdos1030

/--
Let $R(k,l)$ be the usual Ramsey number: the smallest $n$ such that if the edges of $K_n$ are
coloured red and blue then there exists either a red $K_k$ or a blue $K_l$.

Prove the existence of some $c>0$ such that, for all sufficiently large $k$,
$$R(k+1,k) > (1+c)R(k,k).$$

In [Er81, p. 11] Erdős states this as a conjecture of Burr and himself, in the form
$r(n+1,n) > (1+c)r(n,n)$. erdosproblems.com describes it as a problem of Erdős and Sós and
writes it with a $\lim$. In [Er93, p. 339, Eq. (10)] Erdős attributes the conjecture to Vera Sós
and himself and states the same ratio bound. For the literal reading, which additionally requires the ratio to
converge, see `erdos_1030.variants.tendsto`.
-/
@[category research open, AMS 5]
theorem erdos_1030 :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey (k + 1) k : ℝ) >
        (1 + c) * (SimpleGraph.classicalRamsey k k : ℝ) := by
  sorry

/--
The literal reading of the "$\lim$" on erdosproblems.com, which additionally asserts that the
ratio $R(k+1,k)/R(k,k)$ converges. This implies `erdos_1030`, but the converse is not clear:
the eventual bound $R(k+1,k) > (1+c)R(k,k)$ does not by itself give convergence of the ratio.
-/
@[category research open, AMS 5]
theorem erdos_1030.variants.tendsto :
    ∃ c > (0 : ℝ), ∃ L : ℝ,
      Tendsto (fun k : ℕ ↦
        (SimpleGraph.classicalRamsey (k + 1) k : ℝ) /
          (SimpleGraph.classicalRamsey k k : ℝ)) atTop (nhds L) ∧
      L > 1 + c := by
  sorry

-- TODO: Add variants of the problem.

end Erdos1030

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
# Erdős Problem 441

*References:*
- [erdosproblems.com/441](https://www.erdosproblems.com/441)
- [Er51b] P. Erdős, *Problem*. Mat. Lapok (1951), 233.
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189.
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [Ch72b] Choi, S. L. G., *The largest subset in $[1,n]$ whose integers have pairwise L.C.M. not
  exceeding $n$*. Mathematika (1972), 221-230.
- [Ch98] Chen, Yong-Gao, *Sequences with bounded l.c.m. of each pair of terms*. Acta Arith.
  (1998), 71-95.
- [DaCh06] Dai, Li-Xia and Chen, Yong-Gao, *Sequences with bounded l.c.m. of each pair of terms.
  II*. Acta Arith. (2006), 315-326.
- [ChDa07] Chen, Yong-Gao and Dai, Li-Xia, *Sequences with bounded l.c.m. of each pair of terms.
  III*. Acta Arith. (2007), 125-133.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos441

/--
`g N` is the size of the largest `A ⊆ {1, …, N}` such that `lcm(a, b) ≤ N` for all `a, b ∈ A`.
-/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}

/--
Erdős' construction: all integers in $[1,(N/2)^{1/2}]$ together with all even integers in
$[(N/2)^{1/2},(2N)^{1/2}]$.
-/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦ 2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

/--
Let $N\geq 1$. What is the size of the largest $A\subset \{1,\ldots,N\}$ such that $[a,b]\leq N$
for all $a,b\in A$, where $[a,b]$ is the least common multiple of $a$ and $b$?

Is it attained by choosing all integers in $[1,(N/2)^{1/2}]$ together with all even integers in
$[(N/2)^{1/2},(2N)^{1/2}]$?

Let $g(N)$ denote the size of the largest such $A$. The construction mentioned proves that
$g(N) \geq \left(\tfrac{9}{8}N\right)^{1/2}+O(1)$. Erdős [Er51b] proved
$g(N) \leq (4N)^{1/2}+O(1)$, which was improved by Choi [Ch72b]. Chen [Ch98] established the
asymptotic $g(N) \sim \left(\tfrac{9}{8}N\right)^{1/2}$. Chen and Dai [DaCh06] proved that
$$g(N)\leq \left(\tfrac{9}{8}N\right)^{1/2}+
O\left(\left(\frac{N}{\log N}\right)^{1/2}\log\log N\right).$$

In [ChDa07] the same authors prove that, infinitely often, Erdős' construction is not optimal: if
$B$ is that construction and $A$ is such that $\lvert A\rvert=g(N)$ then, for infinitely many
$N$, $\lvert A\rvert\geq \lvert B\rvert+t$, where $t\geq 0$ is defined such that the $t$-fold
iterated logarithm of $N$ is in $[0,1)$.

This is discussed in problems B26 and E2 of Guy's collection [Gu04].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos441.lean#L453"]
theorem erdos_441 : answer(False) ↔
    ∀ N : ℕ, 1 ≤ N → g N = (erdosConstruction N).card := by
  sorry

/--
Chen and Dai [ChDa07] proved that, infinitely often, Erdős' construction is not optimal: for
infinitely many $N$, $g(N) \geq \lvert B\rvert+t$, where $B$ is the construction and $t\geq 0$ is
such that the $t$-fold iterated logarithm of $N$ is in $[0,1)$.
-/
@[category research solved, AMS 11]
theorem erdos_441.variants.chen_dai_infinitely_often :
    ∃ᶠ N : ℕ in atTop, (erdosConstruction N).card + Real.iteratedLog N ≤ g N := by
  sorry

/-- Erdős' construction proves that $g(N) \geq \left(\tfrac{9}{8}N\right)^{1/2}+O(1)$. -/
@[category research solved, AMS 11]
theorem erdos_441.variants.lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, √(9 / 8 * N) - C ≤ g N := by
  sorry

/-- Erdős [Er51b] proved $g(N) \leq (4N)^{1/2}+O(1)$. -/
@[category research solved, AMS 11]
theorem erdos_441.variants.erdos_upper_bound :
    ∃ C : ℝ, ∀ N : ℕ, (g N : ℝ) ≤ √(4 * N) + C := by
  sorry

/-- Chen [Ch98] established the asymptotic $g(N) \sim \left(\tfrac{9}{8}N\right)^{1/2}$. -/
@[category research solved, AMS 11]
theorem erdos_441.variants.chen :
    (fun N : ℕ ↦ (g N : ℝ)) ~[atTop] fun N ↦ √(9 / 8 * N) := by
  sorry

/--
Chen and Dai [DaCh06] proved that
$g(N)\leq \left(\tfrac{9}{8}N\right)^{1/2}+
O\left(\left(\frac{N}{\log N}\right)^{1/2}\log\log N\right)$.
-/
@[category research solved, AMS 11]
theorem erdos_441.variants.chen_dai_upper_bound :
    (fun N : ℕ ↦ (g N : ℝ) - √(9 / 8 * N)) =O[atTop]
      fun N ↦ √(N / Real.log N) * Real.log (Real.log N) := by
  sorry

end Erdos441

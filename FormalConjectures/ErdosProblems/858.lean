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
# Erdős Problem 858

*References:*
- [erdosproblems.com/858](https://www.erdosproblems.com/858)
- [Er70,p.128] Erdős, P., *Some extremal problems in combinatorial number theory*.
  Mathematical Essays Dedicated to A. J. Macintyre (1970), 123-133.
- [Al66] Alexander, Ralph, *Density and multiplicative structure of sets of integers*.
  Acta Arith. (1966/67), 321-332.
- [ESS68] Erdős, P. and Sárközi, A. and Szemerédi, E.,
  *On the solvability of certain equations in sequences of positive upper logarithmic density*.
  J. London Math. Soc. (1968), 71-78.
- [Be35] Behrend, F., *On sequences of numbers not divisible by another*.
  J. London Math. Soc. (1935), 42-45.
- [ChGPT26] G. Chojecki and GPT-5.4 Pro, *The asymptotic constant in Erdős problem #858*.
  [https://www.ulam.ai/research/erdos858-asymptotic.pdf](https://www.ulam.ai/research/erdos858-asymptotic.pdf)
-/

open Asymptotics Filter
open scoped Topology

namespace Erdos858

/--
`A ⊆ {1, …, N}` has no solution of `a * t = b` with `a, b ∈ A` and
`Nat.minFac t > a`. The case `t = 1` (so `a = b`) is allowed, since
`Nat.minFac 1 = 1`.
-/
def Admissible (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ t, a * t = b → ¬ a < t.minFac

/-- The same multiplicative restriction, for (possibly infinite) sets of positive integers. -/
def AdmissibleSet (A : Set ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a) ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ t, a * t = b → ¬ a < t.minFac

/-- A set is primitive if no distinct elements divide one another. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- The reciprocal sum `∑_{n ∈ A} 1/n` of the problem. -/
def reciprocalMass (A : Finset ℕ) : ℚ := ∑ a ∈ A, (1 : ℚ) / a

/-- The largest reciprocal sum `∑_{n ∈ A} 1/n` over admissible `A ⊆ {1, …, N}`. -/
noncomputable def maxMass (N : ℕ) : ℝ :=
  sSup ((fun A => (reciprocalMass A : ℝ)) '' {A : Finset ℕ | Admissible A N})

/-- Integers in `[N^{1/2}, N]` divisible by some prime `> N^{1/2}`. -/
noncomputable def exampleSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n =>
    (N : ℝ).sqrt ≤ n ∧ ∃ p, Nat.Prime p ∧ p ∣ n ∧ (N : ℝ).sqrt < p

/--
Let $A\subseteq \{1,\ldots,N\}$ be such that there is no solution to $at=b$ with $a,b\in A$ and the smallest prime factor of $t$ is $>a$. Estimate the maximum of
$$\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}.$$

This has been solved by Chojecki and GPT-5.4 Pro, who show that for large $N$
$$\max_A \sum_{n\in A}\frac{1}{n}=(c+o(1))\log N$$
where the maximum is over all $A\subseteq \{1,\ldots,N\}$ with the stated property and $c\approx 0.618\cdots$ is an explicit constant.
-/
@[category research solved, AMS 11]
theorem erdos_858 :
    ∃ c > 0, maxMass ~[atTop] fun N => c * Real.log N := by
  sorry

/--
Equivalently, $\frac{1}{\log N}\max_A \sum_{n\in A}\frac{1}{n}$ tends to the same positive constant $c$.
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.tendsto :
    ∃ c > 0, Tendsto (fun N => maxMass N / Real.log N) atTop (nhds c) := by
  sorry

open scoped Classical in
/--
Alexander [Al66] and Erdős, Sárközi, and Szemerédi [ESS68] proved that if $A$ is an infinite set with this property then
$$\sum_{n\in A\cap [1,N]}\frac{1}{n}=o(\log N)$$
(at a rate which depends on $A$).
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.infinite (A : Set ℕ) :
    A.Infinite → AdmissibleSet A →
    (fun N : ℕ => ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n) =o[atTop]
      fun N => Real.log N := by
  sorry

/--
For any fixed large $N$ the supremum in this question is bounded away from $0$.
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.positive :
    ∃ c > 0, ∀ᶠ N : ℕ in atTop, c ≤ maxMass N / Real.log N := by
  sorry

/--
This condition on $A$ is a weaker form of the usual primitive condition. If $A$ is primitive then Behrend [Be35] proved
$$\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}\ll \frac{1}{\sqrt{\log\log N}}.$$
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.behrend :
    ∃ C > 0, ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      IsPrimitive (A : Set ℕ) →
        (reciprocalMass A : ℝ) / Real.log N ≤
          C / Real.sqrt (Real.log (Real.log N)) := by
  sorry

/--
An example of such a set $A$ is the set of all integers in $[N^{1/2},N]$ divisible by some prime $>N^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.example (N : ℕ) : Admissible (exampleSet N) N := by
  sorry

end Erdos858

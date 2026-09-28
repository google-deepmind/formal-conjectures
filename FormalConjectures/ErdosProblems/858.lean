/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 858

*References:*
- [erdosproblems.com/858](https://www.erdosproblems.com/858)
- [Er70] Erdős, Paul, _Some extremal problems in combinatorial number theory_. Mathematical Essays
  Dedicated to A. J. Macintyre (1970), 123-133.
- [Al66] Alexander, Ralph, _Density and multiplicative structure of sets of integers_. Acta
  Arith. (1966/67), 321--332.
- [ESS68] Erdős, P. and Sárközi, A. and Szemerédi, E., _On the solvability of certain equations
  in sequences of positive upper logarithmic density_. J. London Math. Soc. (1968), 71--78.
- [Be35] Behrend, F., _On sequences of numbers not divisible by another_. London Math. Soc.
  Journal (1935), 42-45.
-/

@[expose] public section

open Filter Real

namespace Erdos858

/-- `A` has no solution to $at=b$ with $a,b\in A$ and the smallest prime factor of $t$
greater than $a$. -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a

/-- The maximum of $\sum_{n\in A}\frac{1}{n}$ over all admissible $A\subseteq \{1,\ldots,N\}$. -/
noncomputable def M (N : ℕ) : ℝ :=
  sSup {m | ∃ A ⊆ Finset.Icc 1 N, IsAdmissible A ∧ ∑ n ∈ A, (1 : ℝ) / n = m}

/--
Let $A\subseteq \{1,\ldots,N\}$ be such that there is no solution to $at=b$ with $a,b\in A$ and
the smallest prime factor of $t$ is $>a$. Estimate the maximum of
$$\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}.$$

This has been solved by Chojecki and GPT-5.4 Pro, who show that for large $N$
$$\max_A \sum_{n\in A}\frac{1}{n}=(c+o(1))\log N$$
where the maximum is over all $A\subseteq \{1,\ldots,N\}$ with the stated property and
$c\approx 0.618\cdots$ is an explicit constant.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos858.lean#L4771"]
theorem erdos_858 : ∃ c : ℝ, Tendsto (fun N : ℕ ↦ M N / log N) atTop (nhds c) := by
  sorry

/-- The limit $c\approx 0.618\cdots$ is positive: for any fixed large $N$ the maximum is bounded
away from $0$ (Alexander [Al66], Erdős–Sárközi–Szemerédi [ESS68]). -/
@[category research solved, AMS 11]
theorem erdos_858.variants.positive :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun N : ℕ ↦ M N / log N) atTop (nhds c) := by
  sorry

open scoped Classical in
/--
Alexander [Al66] and Erdős, Sárközi, and Szemerédi [ESS68] proved that if $A$ is an infinite set
with this property then $\sum_{n\in A\cap [1,N]}\frac{1}{n}=o(\log N)$.
-/
@[category research solved, AMS 11]
theorem erdos_858.variants.infinite (A : Set ℕ) (hA : A.Infinite) (h0 : 0 ∉ A)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a) :
    (fun N : ℕ ↦ ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n) =o[atTop]
      fun N : ℕ ↦ log N := by
  sorry

end Erdos858

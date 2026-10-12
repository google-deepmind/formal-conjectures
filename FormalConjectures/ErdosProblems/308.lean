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
# Erdős Problem 308

*References:*
- [erdosproblems.com/308](https://www.erdosproblems.com/308)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [Cr99] Croot, III, Ernest S., _On some questions of Erdős and Graham about Egyptian
  fractions_. Mathematika (1999), 359-372.
-/

@[expose] public section

open Filter Real

namespace Erdos308

/-- `k` is representable as a sum of distinct unit fractions with denominators from
`{1, …, N}`. -/
def IsRepresentable (N k : ℕ) : Prop :=
  ∃ A ⊆ Finset.Icc 1 N, ∑ n ∈ A, (1 : ℚ) / n = k

/-- The set of positive integers representable as a sum of distinct unit fractions with
denominators from `{1, …, N}`. -/
def representable (N : ℕ) : Set ℕ := {k | 0 < k ∧ IsRepresentable N k}

/-- `f N` is the smallest positive integer which is not representable as a sum of distinct unit
fractions with denominators from `{1, …, N}`. -/
noncomputable def f (N : ℕ) : ℕ := sInf {k | 0 < k ∧ ¬ IsRepresentable N k}

/-- `m N = ⌊∑_{n ≤ N} 1/n⌋`. -/
def m (N : ℕ) : ℕ := ⌊harmonic N⌋₊

/--
Let $N\geq 1$. What is the smallest integer not representable as the sum of distinct unit
fractions with denominators from $\{1,\ldots,N\}$?

This was essentially solved by Croot [Cr99] (see `erdos_308.variants.croot`); in particular,
for all sufficiently large $N$, the smallest such integer is either $m_N$ or $m_N+1$, where
$m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.parts.i : ∀ᶠ N : ℕ in atTop, f N = m N ∨ f N = m N + 1 := by
  sorry

/--
Let $N\geq 1$. Is it true that the set of integers representable as the sum of distinct unit
fractions with denominators from $\{1,\ldots,N\}$ has the shape $\{1,\ldots,m\}$ for some $m$?

It follows from Croot's bounds [Cr99] that this holds for all sufficiently large $N$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.parts.ii : answer(True) ↔
    ∀ᶠ N : ℕ in atTop, ∃ m, representable N = Set.Icc 1 m := by
  sorry

/--
If $m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$, then the set of integers representable is, for
all $N$ sufficiently large, either $\{1,\ldots,m_N-1\}$ or $\{1,\ldots,m_N\}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos308.lean#L458"]
theorem erdos_308.variants.shape : ∀ᶠ N : ℕ in atTop,
    representable N = Set.Icc 1 (m N - 1) ∨ representable N = Set.Icc 1 (m N) := by
  sorry

/--
Croot [Cr99] bounded $\eta(N)$, the largest integer such that every integer in
$\{1,\ldots,\eta(N)\}$ is representable; this is $f(N)-1$, so his bounds read
$$\left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{9}{2}(1+o(1))\frac{(\log\log N)^2}{\log N}
\right\rfloor + 1 \leq f(N)$$
and
$$f(N)\leq \left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{1}{2}(1+o(1))
\frac{(\log\log N)^2}{\log N}\right\rfloor + 1.$$
-/
@[category research solved, AMS 11]
theorem erdos_308.variants.croot :
    ∃ o₁ o₂ : ℕ → ℝ, Tendsto o₁ atTop (nhds 0) ∧ Tendsto o₂ atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        ⌊(harmonic N : ℝ) - 9 / 2 * (1 + o₁ N) * (log (log N)) ^ 2 / log N⌋₊ + 1 ≤ f N ∧
        f N ≤ ⌊(harmonic N : ℝ) - 1 / 2 * (1 + o₂ N) * (log (log N)) ^ 2 / log N⌋₊ + 1 := by
  sorry

/--
Is it true that, for every $N\geq 1$, the set of integers representable as the sum of distinct
unit fractions with denominators from $\{1,\ldots,N\}$ has the shape $\{1,\ldots,m\}$ for some
$m$?
-/
@[category research open, AMS 11]
theorem erdos_308.variants.all_N : answer(sorry) ↔
    ∀ N ≥ 1, ∃ m, representable N = Set.Icc 1 m := by
  sorry

end Erdos308

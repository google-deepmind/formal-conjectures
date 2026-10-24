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
# Erdős Problem 1217

*References:*
- [erdosproblems.com/1217](https://www.erdosproblems.com/1217)
- [ABLLPSTT26] B. Alexeev, K. Barreto, Y. Li, J. D. Lichtman, L. Price, J. I. Shah, Q. Tang, and
  T. Tao, *Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond*.
  arXiv:2605.00301 (2026).
- [DaEr51] Davenport, H. and Erdős, P., *On sequences of positive integers*. J. Indian Math.
  Soc. (N.S.) (1951), 19--24. [PDF](https://www.renyi.hu/~p_erdos/1951-07.pdf)
- [ESS66] Erdős, P. and Sárközi, A. and Szemerédi, E., *On divisibility properties of sequences of
  integers*. Studia Sci. Math. Hungar. (1966), 431--435.
  [PDF](https://www.renyi.hu/~p_erdos/1966-09.pdf)
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Erdos1217

/-- The weight $\frac{1}{n\log n}$ for $n \geq 2$, and $0$ for $n \in \{0, 1\}$. The value at
$n = 1$ is a convention (the quotient is undefined as $\log 1 = 0$); it changes the sums below by
at most a constant, which does not affect any $\limsup$ after division by $\log\log x \to \infty$.
-/
noncomputable def doublyHarmonicWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then ((n : ℝ) * Real.log n)⁻¹ else 0

/-- The lower logarithmic density
$$\liminf_{x\to\infty}\frac{1}{\log x}\sum_{n\in A,\ n<x}\frac{1}{n}$$
of a set `A` of natural numbers, with a real cutoff `x`. The sum runs over the positive integers
`n < x` in `A`, written as `1 ≤ n < ⌈x⌉₊`. The `liminf` is taken in `ℝ≥0∞`, and `ENNReal.ofReal`
only changes the (irrelevant) values at small `x`. -/
noncomputable def lowerLogDensity (A : Set ℕ) : ℝ≥0∞ :=
  open scoped Classical in
  liminf (fun x : ℝ ↦ ENNReal.ofReal
    ((∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (· ∈ A), (n : ℝ)⁻¹) / Real.log x)) atTop

/-- The right-hand side of the problem,
$$\limsup_{x\to\infty}\frac{1}{\log\log x}\sum_{n\in A,\ n<x}\frac{1}{n\log n},$$
with a real cutoff `x`, the sum running over the positive integers `n < x` in `A`, and the
`limsup` taken in `ℝ≥0∞` (values at small `x`, where `log (log x) ≤ 0`, are irrelevant). -/
noncomputable def weightedRate (A : Set ℕ) : ℝ≥0∞ :=
  open scoped Classical in
  limsup (fun x : ℝ ↦ ENNReal.ofReal
    ((∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (· ∈ A), doublyHarmonicWeight n) /
      Real.log (Real.log x))) atTop

/-- The left-hand side of the problem for a sequence `c`,
$$\limsup_{x\to\infty}\frac{1}{\log\log x}\sum_{c_i<x}1,$$
where the sum counts the positive integers `n < x` that are values of `c`; for a strictly
increasing sequence of positive integers this is the number of indices `i` with `c i < x`. The
`limsup` is taken in `ℝ≥0∞` because it can be `⊤` (for $c_i = 2^i$). -/
noncomputable def chainRate (c : ℕ → ℕ) : ℝ≥0∞ :=
  open scoped Classical in
  limsup (fun x : ℝ ↦ ENNReal.ofReal
    ((((Finset.Ico 1 ⌈x⌉₊).filter (· ∈ Set.range c)).card : ℝ) /
      Real.log (Real.log x))) atTop

/--
Let $A=\{a_1<a_2<\cdots\}$ be an infinite sequence of positive integers with positive lower
logarithmic density.

Must there exist a sequence $n_1<\cdots$ such that
$$a_{n_i}\mid a_{n_{i+1}}$$
for all $i\geq 1$ and
$$\limsup_{x\to \infty}\frac{1}{\log\log x}\sum_{a_{n_i}<x}1 \geq
  \limsup_{x\to \infty} \frac{1}{\log\log x}\sum_{a_n<x}\frac{1}{a_n\log a_n}?$$

A problem of Erdős, Sárközi, and Szemerédi [ESS66, p. 432, (5)]. The answer is yes, proved by
Alexeev, Barreto, Li, Lichtman, Price, Shah, Tang, and Tao [ABLLPSTT26, Theorem 1.6]. Sequences
are indexed from $0$ here.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217.lean#L86"]
theorem erdos_1217 :
    ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) → 0 < lowerLogDensity (Set.range a) →
      ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, a (n i) ∣ a (n (i + 1))) ∧
        weightedRate (Set.range a) ≤ chainRate (a ∘ n) := by
  sorry

/--
The answer to `erdos_1217` is yes even without the assumption that $A$ has positive lower
logarithmic density [ABLLPSTT26]: it suffices that the doubly harmonic rate on the right-hand
side is positive, which holds whenever the lower logarithmic density is positive.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217.lean#L66"]
theorem erdos_1217.variants.without_density :
    ∀ a : ℕ → ℕ, StrictMono a → 0 < weightedRate (Set.range a) →
      ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, a (n i) ∣ a (n (i + 1))) ∧
        weightedRate (Set.range a) ≤ chainRate (a ∘ n) := by
  sorry

/--
The set form of [ABLLPSTT26, Theorem 1.6]: if $A \subseteq \mathbb{N}$ has positive upper doubly
logarithmic density
$$\Delta=\limsup_{x\to\infty}\frac{1}{\log\log x}\sum_{n\in A,\ n<x}\frac{1}{n\log n},$$
then $A$ contains a strictly increasing infinite divisibility chain $d_0\mid d_1\mid\cdots$ with
$$\limsup_{x\to\infty}\frac{1}{\log\log x}\sum_{d_i<x}1\geq\Delta.$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Resolution.lean#L451"]
theorem erdos_1217.variants.abllpstt (A : Set ℕ) (hA : 0 < weightedRate A) :
    ∃ d : ℕ → ℕ, StrictMono d ∧ (∀ i, d i ∈ A) ∧ (∀ i, d i ∣ d (i + 1)) ∧
      weightedRate A ≤ chainRate d := by
  sorry

/--
Davenport and Erdős [DaEr51] proved that (assuming $A$ has positive lower logarithmic density)
there exists a sequence $n_1<\cdots$ such that $a_{n_i}\mid a_{n_{i+1}}$ for all $i\geq 1$
(as stated in [ESS66, p. 431]). This also follows from `erdos_1217`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217.lean#L86"]
theorem erdos_1217.variants.davenport_erdos :
    ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) → 0 < lowerLogDensity (Set.range a) →
      ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ i, a (n i) ∣ a (n (i + 1)) := by
  sorry

/--
Erdős, Sárközi, and Szemerédi [ESS66, Theorem 2] proved that if
$$\limsup_{x\to \infty}\frac{1}{\log\log x}\sum_{a_n<x}\frac{1}{a_n\log a_n}=c>0,$$
then there exists such a sequence with
$$\limsup_{x\to \infty}\frac{1}{\log\log x}\sum_{a_{n_i}<x}1\gg_c 1.$$
Here $\gg_c 1$ means a lower bound $\kappa>0$ depending only on $c$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217.lean#L66"]
theorem erdos_1217.variants.erdos_sarkozi_szemeredi :
    ∀ c : ℝ, 0 < c → ∃ κ : ℝ, 0 < κ ∧ ∀ a : ℕ → ℕ, StrictMono a →
      weightedRate (Set.range a) = ENNReal.ofReal c →
        ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, a (n i) ∣ a (n (i + 1))) ∧
          ENNReal.ofReal κ ≤ chainRate (a ∘ n) := by
  sorry

end Erdos1217

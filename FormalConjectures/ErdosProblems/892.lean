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

import FormalConjectures.ErdosProblems.«1196»
import FormalConjecturesUtil

/-!
# Erdős Problem 892

*References:*
- [erdosproblems.com/892](https://www.erdosproblems.com/892)
- [ESS67] Erdős, P. and Sárközy, A. and Szemerédi, E., *On a theorem of Behrend*. J. Austral. Math.
  Soc. (1967), 9--16.
- [ESS68] Erdős, P. and Sárközi, A. and Szemerédi, E., *On the solvability of certain equations in
  sequences of positive upper logarithmic density*. J. London Math. Soc. (1968), 71--78.
- [Er35] Erdős, Paul, *Note on Sequences of Integers No One of Which is Divisible By Any Other*.
  J. London Math. Soc. (1935), 126-128.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
-/

open Filter Finset Asymptotics

namespace Erdos892

/--
A sequence `b` is majorized by a primitive sequence if there exists a primitive sequence `a`
(no element divides another) with `a n ≪ b n` for all `n`.
-/
def ExistsPrimitiveMajorizedBy (b : ℕ → ℕ) : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ Erdos1196.IsPrimitive (Set.range a) ∧
    (fun n => (a n : ℝ)) ≪ (fun n => (b n : ℝ))

/--
There are no non-trivial solutions of `(b i, b j) = b k`. Solutions with `k = i` or `k = j` are
regarded as trivial (in particular `gcd (b i) (b i) = b i`).
-/
def NoNontrivialGcdEq (b : ℕ → ℕ) : Prop :=
  ∀ i j k : ℕ, Nat.gcd (b i) (b j) = b k → k = i ∨ k = j

/--
There is a primitive set `A` with `|A ∩ [1, 2^{n i}]| ≫ 2^{n i}` for every `i`.
-/
def ExistsPrimitiveDenseAt (n : ℕ → ℕ) : Prop :=
  ∃ A : Set ℕ, Erdos1196.IsPrimitive A ∧
    ∃ C > (0 : ℝ), ∀ i, C * (2 ^ n i : ℝ) ≤ ((A ∩ Set.Icc 1 (2 ^ n i)).ncard : ℝ)

/--
Is there a necessary and sufficient condition for a sequence of integers $b_1<b_2<\cdots$ that
ensures there exists a primitive sequence $a_1<a_2<\cdots$ (i.e. no element divides another) with
$a_n \ll b_n$ for all $n$?

A problem of Erdős, Sárközi, and Szemerédi [ESS68]. One can ask a similar question for sequences of
real numbers, as in [erdosproblems.com/143](https://www.erdosproblems.com/143). In [Er80] Erdős
suggests the first question is 'difficult and perhaps has no reasonable solution', and perhaps the
final question is more reasonable.
-/
@[category research open, AMS 11]
theorem erdos_892.parts.i :
    let P : (ℕ → ℕ) → Prop := answer(sorry)
    ∀ b : ℕ → ℕ, StrictMono b → (P b ↔ ExistsPrimitiveMajorizedBy b) := by
  sorry

/--
In particular, is this always possible if there are no non-trivial solutions to $(b_i,b_j)=b_k$?
-/
@[category research open, AMS 11]
theorem erdos_892.parts.ii :
    answer(sorry) ↔
      ∀ b : ℕ → ℕ, StrictMono b → NoNontrivialGcdEq b → ExistsPrimitiveMajorizedBy b := by
  sorry

/--
Similarly, find necessary and sufficient conditions on a sequence $n_1<n_2<\cdots$ that ensure
there exists a primitive set $A$ such that
$$\lvert A\cap [1,2^{n_i}]\rvert \gg 2^{n_i}$$
for every $i$.
-/
@[category research open, AMS 11]
theorem erdos_892.parts.iii :
    let P : (ℕ → ℕ) → Prop := answer(sorry)
    ∀ n : ℕ → ℕ, StrictMono n → (P n ↔ ExistsPrimitiveDenseAt n) := by
  sorry

/--
It is known that
$$\sum \frac{1}{b_n\log b_n}<\infty$$
is necessary. This is due to Erdős [Er35].
-/
@[category research solved, AMS 11]
theorem erdos_892.variants.reciprocal_log_sum (b : ℕ → ℕ) (hb : StrictMono b)
    (hb1 : ∀ n, 1 < b n) (h : ExistsPrimitiveMajorizedBy b) :
    Summable fun n => 1 / ((b n : ℝ) * Real.log (b n)) := by
  sorry

/--
It is known that
$$\sum_{b_n<x}\frac{1}{b_n} =o\left(\frac{\log x}{\sqrt{\log\log x}}\right)$$
is necessary. This is due to Erdős, Sárközy, and Szemerédi [ESS67].
-/
@[category research solved, AMS 11]
theorem erdos_892.variants.partial_reciprocal_sum (b : ℕ → ℕ) (hb : StrictMono b)
    (hb1 : ∀ n, 1 < b n) (h : ExistsPrimitiveMajorizedBy b) :
    (fun x : ℕ => ∑ n ∈ (range x).filter (b · < x), (1 : ℝ) / b n) =o[atTop]
      fun x : ℕ => Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  sorry

end Erdos892

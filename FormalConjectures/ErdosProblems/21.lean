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
# Erdős Problem 21

*References:*
- [erdosproblems.com/21](https://www.erdosproblems.com/21)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) (1992), 231-240.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [ErLo75] Erdős, P. and Lovász, L., *Problems and results on $3$-chromatic hypergraphs and some
  related questions*. (1975), 609--627.
- [Ka92b] Kahn, Jeff, *On a problem of Erdős and Lovász: random lines in a projective plane*.
  Combinatorica (1992), 417-423.
- [Ka94] Kahn, Jeff, *On a problem of Erdős and Lovász. II. $n(r)=O(r)$*. J. Amer. Math. Soc.
  (1994), 125-143.
- [Tr14] A. Tripathi, *A result on intersecting families with maximum transversal size*.
  arXiv:1409.4610 (2014).
- [BaWa21] J. Barát and I. M. Wanless, *Intersecting and 2-intersecting hypergraphs with maximal
  covering number: the Erdős-Lovász theme revisited*. J. Combin. Des. (2021), 260-286.
-/

@[expose] public section

open Filter

namespace Erdos21

/-- An Erdős–Lovász family of order `n`: an intersecting family of `n`-sets such that every set
of size at most `n - 1` is disjoint from some member. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
    ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- `f n` is the minimal size of an Erdős–Lovász family of order `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

/--
Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$ of sets of size $n$
(so $A\cap B\neq\emptyset$ for all $A,B\in \mathcal{F}$) with $\lvert \mathcal{F}\rvert=f(n)$
such that any set $S$ with $\lvert S\rvert \leq n-1$ is disjoint from at least one
$A\in \mathcal{F}$.

Is it true that
$$f(n) \ll n?$$

Conjectured by Erdős and Lovász [ErLo75], who proved that
$$\frac{8}{3}n-3\leq f(n) \ll n^{3/2}\log n$$
for all $n$. The upper bound was improved by Kahn [Ka92b] to $f(n) \ll n\log n$. (The upper
bound constructions in both cases are formed by taking a random set of lines from a projective
plane of order $n-1$, assuming $n-1$ is a prime power.)

This problem was solved by Kahn [Ka94] who proved the upper bound $f(n) \ll n$. The Erdős-Lovász
lower bound of $\frac{8}{3}n-O(1)$ has not been improved, and it has been speculated (see e.g.
[Ka94]) that the correct answer is $3n+O(1)$.

It is trivial that $f(1)=1$ and $f(2)=3$. The values $f(3)=6$ and $f(4)=9$ were established by
Tripathi [Tr14]. Barát and Wanless [BaWa21] proved that $f(5)=13$, and that $13\leq f(6)\leq 18$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos21.lean#L13036"]
theorem erdos_21 : answer(True) ↔ ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, f n ≤ C * n := by
  sorry

/-- Erdős and Lovász [ErLo75] proved that $\frac{8}{3}n-3\leq f(n)$ for all $n$. -/
@[category research solved, AMS 5]
theorem erdos_21.variants.lower (n : ℕ) : (8 / 3 : ℝ) * n - 3 ≤ f n := by
  sorry

/-- It has been speculated (see e.g. [Ka94]) that the correct answer is $3n+O(1)$. -/
@[category research open, AMS 5]
theorem erdos_21.variants.three_n : answer(sorry) ↔ ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
    f n ≤ 3 * n + C ∧ 3 * n ≤ f n + C := by
  sorry

/-- $f(1)=1$, $f(2)=3$, $f(3)=6$ [Tr14], $f(4)=9$ [Tr14] and $f(5)=13$ [BaWa21]. -/
@[category research solved, AMS 5]
theorem erdos_21.variants.small_values : f 1 = 1 ∧ f 2 = 3 ∧ f 3 = 6 ∧ f 4 = 9 ∧ f 5 = 13 := by
  sorry

end Erdos21

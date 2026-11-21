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
# Ben Green's Open Problem 59

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.59)
- [Er82] Erdős, P., *Some new problems and results in number theory*. Number theory (Mysore,
  1981), Lecture Notes in Math. 938, Springer (1982), 50--74.
- [Ba89] Balog, A., *On additive representation of integers*. Acta Math. Hungar. 54 (1989),
  297--301.
- [NS08] Naccache, D. and Shparlinski, I. E., *Divisibility, smoothness and cryptographic
  applications*. [arXiv:0810.2067](https://arxiv.org/abs/0810.2067) (2008).
- [DVA21] Dimitrov, V., Vigneri, L. and Attias, V., *Fast generation of RSA keys using smooth
  integers*. IEEE Trans. Comput. (2021).
  [arXiv:1912.11546](https://arxiv.org/abs/1912.11546)
-/

@[expose] public section

open Filter

namespace Green59

/--
`IsSmooth y m` says that every prime factor of `m` is at most `y`.

The numbers $0$ and $1$ have no prime factors (`Nat.primeFactors`), so they are `y`-smooth for
every `y`.
-/
def IsSmooth (y : ℝ) (m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, (p : ℝ) ≤ y

/-- $0$ counts as smooth, which is why `green_59` asks for positive summands. -/
@[category test, AMS 11]
theorem isSmooth_zero (y : ℝ) : IsSmooth y 0 := by
  simp [IsSmooth]

/--
Is every $n \le N$ the sum of two integers, all of whose prime factors are at most
$N^\varepsilon$?

We read this as: for every $\varepsilon > 0$ and every sufficiently large $N$, every integer
$2 \le n \le N$ is $a + b$ with positive integers $a, b$ whose prime factors are all at most
$N^\varepsilon$. Positive summands exclude $n = 1$. [Gr24] quotes Erdős [Er82] for an
essentially equivalent conjecture, which is
[Erdős Problem 334](https://www.erdosproblems.com/334). [Gr24] also reports a remark of Wooley:
a positive answer for every $\varepsilon > 0$ would solve Vinogradov's least quadratic
non-residue problem for primes $p \equiv 3 \pmod 4$.
-/
@[category research open, question, AMS 11]
theorem green_59 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Icc 2 N, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      a + b = n ∧ IsSmooth ((N : ℝ) ^ ε) a ∧ IsSmooth ((N : ℝ) ^ ε) b := by
  sorry

/--
**Balog's theorem.** For every $\varepsilon > 0$, every sufficiently large integer $N$ is
$n_1 + n_2$ with positive integers $n_1, n_2$ whose prime factors are all at most
$N^{4/(9\sqrt{e}) + \varepsilon}$, where $4/(9\sqrt{e}) \approx 0.2695$.

This is due to Balog [Ba89]. We take it from [NS08, Section 6.6], which states it with exponent
$4/(9\sqrt{e})$, and [DVA21, Theorem 4], which states it with exponent
$4/(9\sqrt{e}) + \varepsilon$, as here. Applied to each large $n \le N$ (and with
$n = 1 + (n - 1)$ for small $n$), it gives `green_59` with $\varepsilon$ replaced by any number
greater than $4/(9\sqrt{e})$; [Gr24] says this is still the record.
-/
@[category research solved, AMS 11]
theorem green_59.variants.balog :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      IsSmooth ((N : ℝ) ^ (4 / (9 * Real.sqrt (Real.exp 1)) + ε)) a ∧
      IsSmooth ((N : ℝ) ^ (4 / (9 * Real.sqrt (Real.exp 1)) + ε)) b := by
  sorry

end Green59

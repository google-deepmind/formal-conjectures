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
# Chowla's Conjecture on Correlations of the Liouville Function

For $n \ge 1$, the Liouville function $\lambda(n) = (-1)^{\Omega(n)}$
(`ArithmeticFunction.liouville`) records the parity of the prime-factor count $\Omega(n)$ with
multiplicity. Sarvadaman Chowla [Ch65]
conjectured that for every $k \ge 1$ and any injective tuple of nonnegative shifts
$h_1, \dots, h_k$, the Cesàro correlation $\frac{1}{N} \sum_{n=1}^N \prod_{i=1}^k \lambda(n + h_i)$
tends to $0$ as $N \to \infty$. Wikipedia discusses the nilsequence equivalence for averaged
correlations; the exact statements below follow [Ch65], Matomäki–Radziwiłł–Tao [MRT15], and Tao
[Ta16]. Unweighted $k$-point correlations remain open for every $k \ge 2$.

*References:*
- [Wikipedia: Nilsequence](https://en.wikipedia.org/wiki/Nilsequence)
- [Wikipedia: Liouville function](https://en.wikipedia.org/wiki/Liouville_function)
- [La09] E. Landau, *Handbuch der Lehre von der Verteilung der Primzahlen*, Vol. 2, Teubner,
  Leipzig, 1909, §157.
- [Ch65] S. Chowla, *The Riemann Hypothesis and Hilbert's Tenth Problem*, Gordon and Breach,
  New York, 1965.
- [MRT15] K. Matomäki, M. Radziwiłł, and T. Tao, *An averaged form of Chowla's conjecture*,
  Algebra & Number Theory **9** (2015), no. 9, 2167–2196.
- [Ta16] T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
  correlations*, Forum Math. Pi **4** (2016), e8, 1–36.
-/

@[expose] public section

namespace ChowlaLiouvilleConjecture

/-- **Chowla's Conjecture** [Ch65]: for every $k \ge 1$ and every injective shift tuple
`h : Fin k → ℕ`, the Cesàro average $\frac{1}{N} \sum_{n=1}^N \prod_{i < k} \lambda(n + h_i)$
tends to $0$ as $N \to \infty$. The hypothesis `1 ≤ k` excludes the empty product $1$, and
injectivity excludes repeated factors $\lambda(n + h)^2 = 1$. -/
@[category research open, AMS 11]
theorem chowla_liouville_conjecture (k : ℕ) (hk : 1 ≤ k) (h : Fin k → ℕ)
    (hh : Function.Injective h) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N, ∏ i : Fin k, (ArithmeticFunction.liouville (n + h i) : ℝ)) /
          (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

/-- **One-Point Liouville Average** [La09]: the $k = 1$ case
$\frac{1}{N} \sum_{n=1}^N \lambda(n) \to 0$, equivalent to PNT. -/
@[category research solved, AMS 11]
theorem chowla_liouville_conjecture.variants.one_point :
    Filter.Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

/-- **Shift-Averaged Two-Point Chowla Theorem** [MRT15]: the average over shifts $1 \le h \le H$ of
$\left|\frac{1}{N} \sum_{n=1}^N \lambda(n)\lambda(n + h)\right|$ becomes arbitrarily small for
sufficiently large $H$ and $N$. -/
@[category research solved, AMS 11]
theorem chowla_liouville_conjecture.variants.averaged_two_point (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in Filter.atTop, ∀ᶠ N : ℕ in Filter.atTop,
      (∑ h ∈ Finset.Icc 1 H,
        |∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
            (N : ℝ)) / (H : ℝ) < ε := by
  sorry

/-- **Logarithmically Averaged Two-Point Chowla Theorem** [Ta16]: for every shift $a \ge 1$,
$\frac{1}{\log N} \sum_{n=1}^N \frac{\lambda(n)\lambda(n + a)}{n} \to 0$ as $N \to \infty$. -/
@[category research solved, AMS 11]
theorem chowla_liouville_conjecture.variants.logarithmic_two_point (a : ℕ) (ha : 1 ≤ a) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + a) : ℝ) / (n : ℝ)) /
            Real.log (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end ChowlaLiouvilleConjecture

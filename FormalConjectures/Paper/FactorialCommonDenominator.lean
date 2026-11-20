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
# Least common multiples of factorial-gap denominators

The least common multiple of the numbers $n!-1$ through $N$ has logarithm at least
$(2\sqrt2/3-o(1))N^{3/2}\log N$ [Co26].

The factorial-gap gcd subtraction used in the argument is the $P=-1$ specialization
of the shifted-factorial relation of Luca and Shparlinski [LS05], also recorded
by Lai [La21].

*References:*
- [Co26] W. Cook, *Factorial Linear Forms and Denominators: Detailed Proofs and
  Rationality Criteria*, common-denominator growth theorem,
  [source](https://github.com/wcook04/plectis-erdos/blob/6db987f4a843ae40ab07ac782ef0cca1a95815c1/paper/68/erdos68-factorial-reasoning-surface.tex#L1066-L1104).
- [LS05] F. Luca and I. E. Shparlinski, *Prime divisors of shifted factorials*,
  Bull. London Math. Soc. 37 (2005), 809–817, proof of Lemma 5,
  [doi](https://doi.org/10.1112/S0024609305004923).
- [La21] L. Lai, *On the largest prime divisor of $n!+1$*, proof of Lemma 2.4,
  display (2.5), [arXiv:2103.14894v1](https://arxiv.org/abs/2103.14894v1).
-/

@[expose] public section

open Filter

namespace FactorialCommonDenominator

/-- The least common multiple $L_N=\operatorname{lcm}_{2\le n\le N}(n!-1)$.
The empty least common multiple is one. -/
def channelLCM (N : ℕ) : ℕ :=
  (Finset.Icc 2 N).lcm (fun n => n.factorial - 1)

/-- The factorial-gap common denominator satisfies
$$
  \liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}\ge\frac{2\sqrt2}{3}.
$$
The lower limit is taken in the extended reals and may be $+\infty$.
This is the common denominator before cancellation in the partial sums of
$\sum_{n\ge2}1/(n!-1)$; the theorem gives no irrationality conclusion.
-/
@[category research solved, AMS 11 40,
  formal_proof using lean4 at "https://github.com/wcook04/plectis-erdos-lean/blob/71a2bc9f74f8650d7287581f799ba998fe26e60f/verification/FC68CommonDenominatorCurrent/FC68CommonDenominatorSolution.lean#L16-L22"]
theorem growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  sorry

end FactorialCommonDenominator

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
# Erdős Problem 334

*References:*
- [erdosproblems.com/334](https://www.erdosproblems.com/334)
- [Ba89] Balog, A., *On additive representation of integers*. Acta Math. Hungar.
  (1989), 297–301.
-/

@[expose] public section

namespace Erdos334

/--
Find the best function $f(n)$ such that every $n$ can be written as $n=a+b$ where
both $a,b$ are $f(n)$-smooth (that is, are not divisible by any prime $p>f(n)$.)

`F` records the least natural smoothness threshold. It describes positive summands
for $n \geq 2$; the values at $n=0,1$ are set to $0$.
-/
@[category research open, AMS 11]
theorem erdos_334 : F = answer(sorry) := by
  sorry

/--
It is likely that $f(n)\leq n^{o(1)}$.
-/
@[category research open, AMS 11]
theorem erdos_334.variants.subpolynomial : SubpolynomialConjecture := by
  sorry

/--
The best bound is due to Balog [Ba89] who proved that
$$f(n) \ll_\epsilon n^{\frac{4}{9\sqrt{e}}+\epsilon}$$
for all $\epsilon>0$.
-/
@[category research solved, AMS 11]
theorem erdos_334.variants.balog : BalogBound := by
  sorry

/--
Erdős originally asked if even $f(n)\leq n^{1/3}$ is true. This is known.
-/
@[category research solved, AMS 11]
theorem erdos_334.variants.one_third : OneThirdBound := by
  sorry

end Erdos334

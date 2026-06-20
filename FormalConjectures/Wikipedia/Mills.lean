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

import FormalConjectures.Util.ProblemImports

/-!
# Mills' Theorem

There is a real constant $A > 1$ such that
$\lfloor A^{3^n}\rfloor$ is prime for every positive integer $n$, where $\lfloor\cdot\rfloor$
denotes the floor function.

The least such $A$ is known as *Mills' constant*. It is irrational, and assuming the
Riemann hypothesis it is approximately $1.3063778838\ldots$, and it has recently been shown
to be irrational.

*References:*
- [Wikipedia, Mills' constant](https://en.wikipedia.org/wiki/Mills%27_constant)
- [Prime-represntations](https://www.ams.org/journals/bull/1947-53-06/S0002-9904-1947-08849-2/)
  by *W. H. Mills*, Bull. Amer. Math. Soc. **53** (1947), 604.
- [Mills' constant](https://mathworld.wolfram.com/MillsConstant.html) on Wolfram MathWorld.
- [Mills' constant is irrational](https://doi.org/10.1112/mtk.70027) by *Kota Saito*,
  Mathematika **71** (2025), no. 3, e70027, [arXiv:2404.19461](https://arxiv.org/abs/2404.19461).
- [Determining Mills' Constant ..](https://cs.uwaterloo.ca/journals/JIS/VOL8/Caldwell/caldwell78.pdf)
  by *Chris K. Caldwell and Yuanyou Cheng*, J. Integer Seq. **8** (2005), Article 05.4.1.
- [OEIS A051021](https://oeis.org/A051021) (decimal expansion of Mills' constant)
-/

namespace Mills

abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/--
**Mills' theorem** (Mills, 1947).
There is a real number $A > 1$ such that $\lfloor A^{3^n}\rfloor$ is prime.
-/
@[category research solved, AMS 11]
theorem exists' : ∃ A > 1, IsMills A := by
  sorry

abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/--
**Mills' constant.**
There is a *least* Mills number.
-/
@[category research solved, AMS 11]
theorem exists_least : ∃ A, IsMinMills A := by
  sorry

/--
**Mills' constant is irrational** (Saito, 2024): the least Mills number is irrational.
-/
@[category research solved, AMS 11]
theorem irrational {A} (hA : IsMinMills A) :
    Irrational A := by
  sorry

/--
**Mills' constant** (Caldwell–Cheng, 2005): assuming the Riemann hypothesis, the least
Mills number begins $1.3063778838\ldots$.
-/
@[category research solved, AMS 11]
theorem mills.variants.approx (hRH : RiemannHypothesis) {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry

end Mills

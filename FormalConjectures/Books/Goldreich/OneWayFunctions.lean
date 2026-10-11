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
# Existence of nonuniformly one-way functions

The function is computed by one polynomial-time deterministic multitape machine.
Every polynomial-size circuit adversary has negligible inversion probability.
Length preservation follows the convention in Goldreich, Section 2.2.3; no injectivity
is required.

*Reference:* Oded Goldreich, *Foundations of Cryptography, Volume 1: Basic Tools*,
Cambridge University Press, 2001, Sections 2.2.3 and 2.2.5.
See also Definition 2.6 in the
[author's Chapter 2 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part2.pdf).
-/

@[expose] public section

namespace ComplexityTheory

/-- There exists a polynomial-time, length-preserving function $f$ such that every
polynomial-size circuit family $C_n$ has negligible probability of finding any preimage:
$\Pr_{x\sim U_n}[f(C_n(f(x)))=f(x)]\le n^{-b}$ eventually, for every $b\in\mathbb{N}$.
The nonuniform convention is from Goldreich, Section 2.2.5. -/
@[category research open, AMS 68 94]
theorem exists_one_way_function : ∃ f, OneWay f := by
  sorry

end ComplexityTheory

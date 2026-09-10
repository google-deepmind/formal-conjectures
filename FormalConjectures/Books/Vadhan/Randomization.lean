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
import FormalConjecturesUtil

/-!
# Eliminating randomness from polynomial-time decision algorithms

Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer
Science 7(1–3), 2012, §2.2:
https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.

Definitions 2.9 and 2.13 specify the one- and two-sided error conventions.
Definition 2.15 gives the expected-time Las Vegas model; the formal ZPP class
uses its equivalent characterization in Fact 2.16, $\mathrm{RP}\cap\mathrm{coRP}$.
All classes here have actual polynomial-time TM2 machines and polynomially many
uniform independent random bits. These are three different questions, not three
claimed equivalents of $\mathrm{P}\ne\mathrm{NP}$.
-/

namespace VadhanPseudorandomness

/-- Does $\mathrm{BPP}=\mathrm{P}$? Open Problem 2.14, p. 20. -/
@[category research open, AMS 3 68]
theorem bpp_eq_p : answer(sorry) ↔ ComplexityTheory.BPP = ComplexityTheory.P := by
  sorry

/-- Does $\mathrm{P}=\mathrm{RP}$? Open Problem 2.10, p. 19. -/
@[category research open, AMS 3 68]
theorem p_eq_rp : answer(sorry) ↔ ComplexityTheory.P = ComplexityTheory.RP := by
  sorry

/-- Does $\mathrm{P}=\mathrm{ZPP}$? The first inclusion in Open Problem 2.17, p. 21. -/
@[category research open, AMS 3 68]
theorem p_eq_zpp : answer(sorry) ↔ ComplexityTheory.P = ComplexityTheory.ZPP := by
  sorry

end VadhanPseudorandomness

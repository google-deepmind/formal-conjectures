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
# Minimum De Morgan formula size

*References:*
* Ilango, *The Minimum Formula Size Problem is (ETH) Hard*, FOCS 2021,
  pp. 437–446, https://doi.org/10.1109/FOCS52979.2021.00050;
  author version, Theorem 4 and §2, pp. 6–7, https://rahulilango.com/papers/MFSP-hard.pdf.
-/

namespace Ilango2021

/-- **Minimum formula size** (Ilango, §2, pp. 6–7) has no deterministic polynomial
bit-time decider. Input: binary arity $n$, a full $2^n$-bit truth table and a binary
natural bound $s$. Property: a binary AND/OR tree with constant or signed-variable
leaves computes that table using at most $s$ nonconstant leaves. Sharing is not
allowed. Incorrect table lengths are rejected; $s=0$ represents exactly constant
functions, including at $n=0$. Time is measured in the full encoded input length.
Theorem 4 implies this lower bound under ETH, not a stated equivalence to $P\ne NP$. -/
@[category research open, AMS 68]
theorem minimumFormula_not_polytime : ¬
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumFormula := by
  sorry

end Ilango2021

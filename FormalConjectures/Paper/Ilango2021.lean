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

Ilango, *The Minimum Formula Size Problem is (ETH) Hard*, FOCS 2021,
pp. 437–446, https://doi.org/10.1109/FOCS52979.2021.00050.
The author's full version defines formulas and their size in §2, pp. 6–7:
https://rahulilango.com/papers/MFSP-hard.pdf.

Witnesses are trees, not circuits with shared subexpressions. Internal gates are
binary AND/OR; leaves are constants or signed variables. Size counts only
nonconstant leaves. The full table and a binary natural-number bound are input.
At bound zero, exactly constant functions are representable. The source proves
conditional ETH-hardness; it does not settle this unconditional question.
-/

namespace Ilango2021

/-- Does the full-truth-table Minimum Formula Size Problem, with nonconstant
leaf count, admit a deterministic polynomial-time decider? -/
@[category research open, AMS 3 68]
theorem minimumFormula_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumFormula := by
  sorry

end Ilango2021

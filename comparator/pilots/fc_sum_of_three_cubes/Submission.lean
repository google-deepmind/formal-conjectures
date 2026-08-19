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

import ChallengeDeps
import Submission.Helpers

/-!
Trusted smoke submission for the integration harness.

The open-conjecture target deliberately uses the proposition itself as the
definition-hole value and proves the bridge by reflexivity. Comparator should
accept this shape, while a human semantic reviewer must reject it as a
mathematical resolution. That is the definition-hole threat model this pilot
is meant to preserve.
-/

namespace Submission.SumOfThreeCubes

def isSumOfThreeCubes_iff_mod_9_answer : Prop :=
  ∀ n : ℤ,
    _root_.SumOfThreeCubes.IsSumOfThreeCubes n ↔
      ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])

theorem isSumOfThreeCubes_2 :
    _root_.SumOfThreeCubes.IsSumOfThreeCubes (2 : ℤ) := by
  exact ⟨1, 1, 0, by norm_num⟩

theorem isSumOfThreeCubes_iff_mod_9 :
    isSumOfThreeCubes_iff_mod_9_answer ↔
      ∀ n : ℤ,
        _root_.SumOfThreeCubes.IsSumOfThreeCubes n ↔
          ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) :=
  Iff.rfl

end Submission.SumOfThreeCubes

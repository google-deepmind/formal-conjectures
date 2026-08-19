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
import Submission

namespace SumOfThreeCubes

@[reducible] noncomputable def isSumOfThreeCubes_iff_mod_9_answer : Prop :=
  Submission.SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9_answer

theorem isSumOfThreeCubes_2 :
    IsSumOfThreeCubes (2 : ℤ) :=
  Submission.SumOfThreeCubes.isSumOfThreeCubes_2

theorem isSumOfThreeCubes_iff_mod_9 :
    isSumOfThreeCubes_iff_mod_9_answer ↔
      ∀ n : ℤ,
        IsSumOfThreeCubes n ↔
          ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) :=
  Submission.SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9

end SumOfThreeCubes

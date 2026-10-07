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

import RHKreinL105TailV1

/-! Parameters of the `L = 21/20` wide cells.  AUTHORITY_EFFECT = NONE. -/

namespace AEGIS.RHKreinL105BatchV1
open AEGIS.RHKreinL105CheckerV1
def paH (N : ℕ) : Params := ⟨⟨36, 30, 12, 120⟩, 36, 40, N⟩
def paL (N : ℕ) : Params := ⟨⟨16, 30, 12, 120⟩, 16, 40, N⟩
end AEGIS.RHKreinL105BatchV1

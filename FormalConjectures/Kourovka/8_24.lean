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
# Conjecture 8.24.

by V. M. Kopytov

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46)
-/

@[expose] public section

namespace Kourovka«8.24»


/-- Prove that every lineraly ordered group of finite rank is soluble. -/

@[category research solved, question, AMS20]
theorem Kourovka_8_24 (G : Type) [G : Group]:
  ∀ r : G → G → Prop → IslinearOrder G r → IsSolvable G  := by
  sorry

end Kourovka«8.24»

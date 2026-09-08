/-
Copyright 2025 The Formal Conjectures Authors.

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
/-! Check the excluded boundary; this does not prove Goldbach's conjecture. -/
namespace ReviewControl
@[category test, AMS 11]
theorem no_prime_pair_at_two : ¬ ∃ p q : ℕ, Prime p ∧ Prime q ∧ 2 = p + q := by
  rintro ⟨p, q, hp, hq, hsum⟩
  have hp2 := hp.nat_prime.two_le
  have hq2 := hq.nat_prime.two_le
  omega
#print axioms no_prime_pair_at_two
end ReviewControl

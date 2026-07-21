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
# Prime Triplet Conjecture

*Reference:* [Prime Triplet Wikipedia Page](https://en.wikipedia.org/wiki/Prime_triplet#Conjecture_on_prime_triplets)
-/

namespace PrimeTriplets

/--
Are there infinitely many tuples of three consecutive primes $(p, q, r)$ such that $r - p = 6$?
-/
@[category research open, AMS 11]
theorem prime_triplets :
  answer(sorry) ↔ {p : ℕ | Prime p ∧ (Prime (p + 2) ∨ Prime (p + 4)) ∧ Prime (p + 6)}.Infinite := by
    sorry

end PrimeTriplets

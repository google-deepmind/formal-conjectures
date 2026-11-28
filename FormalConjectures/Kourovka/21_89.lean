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
# Conjecture 21.89

by D. MacHale

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v50), Problem 21.89.
- [OEIS A046668](https://oeis.org/A046668)
- R. Heffernan and D. MacHale, *The genesis of a conjecture in number theory*,
  Irish Math. Soc. Bull. 93 (2024), 39–41,
  [doi:10.33232/BIMS.0093.39.41](https://doi.org/10.33232/BIMS.0093.39.41).
-/

@[expose] public section

namespace Kourovka.«21.89»

/--
For $n>39$, is it true that the number of conjugacy classes in the symmetric group $S_n$ of
degree $n$ is never a divisor of the order of $S_n$? In other words, is it true that, for
$n>39$, the number $p(n)$ of integer partitions of $n$ is never a divisor of $n!$?
-/
@[category research open, question, AMS 11 20]
theorem kourovka_21_89 :
    ∀ n > 39, ¬ (Nat.partitionNumber n) ∣ n.factorial := by
  sorry

end Kourovka.«21.89»

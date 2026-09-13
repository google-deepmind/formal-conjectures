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
# Erdős Problem 909

*References:*
- [erdosproblems.com/909](https://www.erdosproblems.com/909)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
- [AnKe67] Anderson, R. D. and Keisler, J. E., *An example in dimension theory*. Proc. Amer.
  Math. Soc. (1967), 709--713.
-/

namespace Erdos909

/--
Let $n\geq 2$. Is there a space $S$ of dimension $n$ such that $S^2$ also has dimension $n$?

The space of rational points in Hilbert space has this property for $n=1$. This was proved for
general $n$ by Anderson and Keisler [AnKe67].
-/
@[category research solved, AMS 54]
theorem erdos_909 :
    answer(True) ↔
      ∀ n ≥ 2, ∃ (S : Type) (_ : TopologicalSpace S),
        smallInductiveDimension S = n ∧ smallInductiveDimension (S × S) = n := by
  sorry

end Erdos909

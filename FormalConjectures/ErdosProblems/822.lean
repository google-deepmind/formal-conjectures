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
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 822

Does the set of integers of the form `n + φ(n)` have positive (lower) density?
Gabdullin, Iudelevich, and Luca proved this was true.

*Reference:* [erdosproblems.com/822](https://www.erdosproblems.com/822)
-/

namespace Erdos822

/--
**Erdős Problem 822.**

Does the set of integers of the form $n + \varphi(n)$ have positive (lower) density?

The problem is known to have an affirmative answer.
-/
@[category research solved, AMS 11]
theorem erdos_822 :
    (Set.range fun n => n + Nat.totient n).HasPosDensity ↔ answer(True) := by
  -- TODO: Replace `sorry` with a formal proof using the results of
  -- Gabdullin–Iudelevich–Luca once an appropriate library interface is available.
  sorry

end Erdos822


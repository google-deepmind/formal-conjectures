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
# Normality of mathematical constants

Despite extensive empirical evidence—billions of digits have been computed for $\pi$,
$e$, and $\sqrt{2}$, all showing near-uniform digit distribution—it is an open problem
whether any of the classical constants $\pi$, $e$, $\sqrt{2}$, $\ln 2$, or $\varphi$ is
normal in any base.

*References:*
* [Wikipedia (Normal number)](https://en.wikipedia.org/wiki/Normal_number)
* [Wikipedia (Pi)](https://en.wikipedia.org/wiki/Pi)
-/

open Real

namespace NormalNumber

/--
$\pi$ is normal in base 10.
-/
@[category research open, AMS 11]
theorem pi_normal_base_ten : IsNormalInBase 10 π := by
  sorry

end NormalNumber

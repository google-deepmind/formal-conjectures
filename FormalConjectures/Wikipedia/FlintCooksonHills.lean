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

import FormalConjectures.Util.ProblemImports

/-!
# Convergence of the Flint Hills and Cookson Hills series

*References:*
- [MathWorld: Flint Hills Series](https://mathworld.wolfram.com/FlintHillsSeries.html)
- [Alekseyev, On the Flint Hills series](https://doi.org/10.48550/arXiv.1104.5100)
- [MathWorld: Cookson Hills Series](https://mathworld.wolfram.com/CooksonHillsSeries.html)
-/

namespace FlintCooksonHills

/--
The Flint Hills series summing $csc(n)^2 / n^3$ from n=1 to ∞ converges.
(Note that we 0-index the series below.)
-/
@[category research open, AMS 40]
theorem flint_hills_series_converges :
    answer(sorry) ↔
      Summable (fun n : ℕ =>
        1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2))) := by
  sorry

/--
The Cookson Hills series summing $sec(n)^2 / n^3$ from n=1 to ∞ converges.
-/
@[category research open, AMS 40]
theorem cookson_hills_series_converges :
    answer(sorry) ↔
      Summable (fun n : ℕ =>
        1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2))) := by
  sorry

end FlintCooksonHills

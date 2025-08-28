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
# Erdős Problem 324

*Reference:* [erdosproblems.com/324](https://www.erdosproblems.com/324)
-/

open scoped Polynomial

namespace Erdos324

/--
Does there exist a polynomial $f(x)\in\mathbb{Z}[x]$ such that all the sums $f(a)+f(b)$ with
$a < b$ nonnegative integers are distinct?
-/
@[category research open, AMS 11]
theorem erdos_324 : (∃ f : ℤ[X],
    {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ))
    ↔ answer(sorry) := by
  sorry

/--
Probably $f(x) = x^5$ has the property that the sums $f(a)+f(b)$ with
$a < b$ nonnegative integers are distinct.
-/
@[category research open, AMS 11]
theorem erdos_324.variant.quintic : {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => a ^ 5 + b ^ 5 := by
  sorry

end Erdos324

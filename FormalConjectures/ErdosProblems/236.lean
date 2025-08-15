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
# Erdős Problem 236

*Reference:* [erdosproblems.com/236](https://www.erdosproblems.com/236)
-/

open Filter Asymptotics

/-- 
$f(n)$ counts the number of solutions to $n=p+2^k$ for prime $p$ and $k\geq 0$.
-/
private def f (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter (fun k => Nat.Prime (n - 2^k))).length

/--
Let $f(n)$ count the number of solutions to $n=p+2^k$ for prime $p$ and $k\geq 0$. Show that $f(n)=o(\log n)$.
-/
@[category research open, AMS 5 11]
theorem erdos_236: (fun n => (f n : ℝ)) =o[atTop] (fun n => Real.log (n : ℝ)) := by 
  sorry

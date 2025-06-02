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

open scoped Polynomial

/-!
# Mathoverflow 21003

Is there any polynomial $f(x, y) \in \mathbb{Q}[x, y]$ such that
$f : \mathbb{Q} \times \mathbb{Q} \rightarrow \mathbb{Q}$ is a bijection?

*Reference:* [mathoverflow/21003](https://mathoverflow.net/questions/21003)
asked by user [*Z.H.*](https://mathoverflow.net/users/5098/z-h)
-/

/--
Is there any polynomial $f(x, y) \in \mathbb{Q}[x, y]$ such that
$f : \mathbb{Q} \times \mathbb{Q} \rightarrow \mathbb{Q}$ is a bijection?
-/
@[category research open, AMS 12]
theorem mathoverflow_21003 :
    (∃ f : MvPolynomial (Fin 2) ℚ, Function.Bijective fun x ↦ f.eval x) ↔ answer(sorry) := by
  sorry

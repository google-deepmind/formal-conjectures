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
# Conjecture 12.55

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

open GroupNumberFunction

namespace Kourovka.«12.55»

/--
Let $f(n, p)$ denote the number of groups of order $p^n$. Is $f(n, p)$,
for fixed $n \geq 5$, an increasing function of $p$?

Here $f(n, p)$ is `groupNumber (p ^ n)`, the number of non-isomorphic groups of order $p^n$.
-/
@[category research open, AMS 20]
theorem kourovka.«12.55» : answer(sorry) ↔
    ∀ n : ℕ, 5 ≤ n →
      ∀ᵉ (p : ℕ) (q : ℕ) (_ : p.Prime) (_ : q.Prime), p < q →
        groupNumber (p ^ n) < groupNumber (q ^ n) := by
  sorry

end Kourovka.«12.55»

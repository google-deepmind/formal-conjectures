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
# Erdős Problem 987

*References:*
- [erdosproblems.com/987](https://www.erdosproblems.com/987)
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math.
  (1964), 52-65.
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974).
-/

open Filter Complex

namespace Erdos987

/--
Let $x_1,x_2,\ldots \in (0,1)$ be an infinite sequence and let
$$A_k=\limsup_{n\to\infty}\left|\sum_{j\leq n}e(kx_j)\right|,$$
where $e(x)=e^{2\pi i x}$. Is it true that
$$\limsup_{k\to\infty} A_k=\infty?$$

The theorem below uses the equivalent formulation in terms of points `z_j` on the unit circle.
-/
@[category research solved, AMS 11 42,
formal_proof using lean4 at
"https://github.com/teorth/analysis/blob/0db7b2b571ca8246082822f8e9483d6568222eac/Analysis/Misc/erdos_987.lean#L12"]
theorem erdos_987 : answer(True) ↔
    ∀ z : ℕ → Circle,
      atTop.limsup (fun k : ℕ =>
        atTop.limsup (fun n : ℕ =>
          (‖∑ j ∈ Finset.range n, ((z j) ^ k : ℂ)‖ : EReal))) = ⊤ := by
  sorry

end Erdos987

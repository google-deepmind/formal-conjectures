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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 906

*References:*
- [erdosproblems.com/906](https://www.erdosproblems.com/906)
- [Hou26] E. Hou, *Cofinite Zeros of High Derivatives* (2026),
  [arXiv:2607.20816](https://arxiv.org/abs/2607.20816).
-/

@[expose] public section

namespace Erdos906

/--
Does there exist an entire non-zero transcendental function `f : ℂ → ℂ` such that for any
sequence `n₀ < n₁ < ...`, `{ z | ∃ k, iteratedDeriv (n k) f z = 0 }` is dense?

The answer is yes: Hou [Hou26] constructed a transcendental entire function of order two with
the stronger property that every nonempty open subset of ℂ contains a zero of $f^{(n)}$ for all
sufficiently large `n`; a strictly increasing sequence is unbounded, so this implies the
dense-set property for every strictly increasing sequence.
-/
@[category research solved, question, AMS 30]
theorem erdos_906 : ∃ f : ℂ → ℂ, Transcendental (Polynomial ℂ) f ∧
    Differentiable ℂ f ∧ ∀ n : ℕ → ℕ, StrictMono n →
    Dense { z | ∃ k, iteratedDeriv (n k) f z = 0 } := by
  sorry

end Erdos906

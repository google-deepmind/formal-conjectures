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

module

public import FormalConjecturesUtil

/-!
# Erdős Problem 491

*References:*
- [erdosproblems.com/491](https://www.erdosproblems.com/491)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
- [Wi70] E. Wirsing, A characterization of $\log n$ as an additive arithmetic function.
  Symposia Math. (1970), 45-57.
-/

@[expose] public section

open Filter

namespace Erdos491

/--
Let $f : \mathbb{N} \to \mathbb{R}$ be an additive function (so that $f(ab) = f(a) + f(b)$
whenever $(a, b) = 1$). If $|f(n+1) - f(n)| < c$ for some constant $c$ and all $n$, then must
there exist some $c'$ such that $f(n) = c' \log n + O(1)$?

A question of Erdős [Er61, p.237; Er82e, p.65], who had proved that $f(n) = c' \log n$ under the
stronger hypotheses $f(n+1) - f(n) = o(1)$ or $f(n+1) \ge f(n)$. The answer is yes, proved by
Wirsing [Wi70]. See also `erdos_897.variants.log_growth`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos491.lean#L34"]
theorem erdos_491 : answer(True) ↔
    ∀ (f : ℕ → ℝ), (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
      (∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < C) →
      ∃ c : ℝ, (fun n : ℕ ↦ f n - c * Real.log n) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
  sorry

end Erdos491

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
# Erdős Problem 289

*References:*
- [erdosproblems.com/289](https://www.erdosproblems.com/289)
- [Ku+26] Kung, P.-N., Song, L., Hwang, D., Yoon, J., Li, C.-L., Severini, S., Olšák, M.,
  Lockhart, E., Le, Q. V., Gokturk, B., Luong, T., Pfister, T., & Peng, N. (2026). _LEAP:
  Supercharging LLMs for Formal Mathematics with Agentic Frameworks_.
  [arXiv:2606.03303](https://arxiv.org/abs/2606.03303).
-/

@[expose] public section

open Asymptotics Filter Finset

namespace Erdos289

/-- Is it true that, for all sufficiently large $k$, there exist finite intervals
$I_1, \dotsc, I_k \subset \mathbb{N}$, distinct, not overlapping or adjacent, with
$|I_i| \geq 2$ for $1 \leq i \leq k$ such that
$$
1 = \sum_{i=1}^k \sum_{n \in I_i} \frac{1}{n}?
$$
Here two intervals are adjacent if their union is again an interval, so any two of the
$I_i$ must be separated by at least one integer.

This is true: a formal proof in Lean 4 was produced by the LEAP prover agent [Ku+26]
(see the linked `formal_proof`). We note that other recent solutions were also posted ahead of
this one (see [erdosproblems.com/forum/thread/289/proof-claims](https://www.erdosproblems.com/forum/thread/289/proof-claims));
this formalization follows an independent, different proof path.
-/
@[category research solved, AMS 11,
  formal_proof using formal_conjectures at
    "https://github.com/lfsong-google/formal-conjectures/blob/ff33e501bb78a90ae4703e22e052f8bb38e10146/FormalConjectures/ErdosProblems/289.lean#L9514"]
theorem erdos_289 : answer(True) ↔
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  sorry

end Erdos289

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
# Erdős Problem 689
*References:*
- [erdosproblems.com/689](https://www.erdosproblems.com/689)
- [Ben Green's Open Problem 45](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.45)
- [Ch26] Chojecki, P., *A greedy matching proof of Erdős's two-fold residue-class problem*.
  [ulam.ai/research/erdos689.pdf](https://www.ulam.ai/research/erdos689.pdf) (April 2026).
- [PALOMAR-2026-09-20-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-20-000002&version=1)
-/

@[expose] public section

namespace Erdos689

/--
Let `n` be sufficiently large. Is there some choice of congruence class `a_p` for all primes
`2 ≤ p ≤ n` such that every integer in `[1,n]` satisfies at least two of the congruences
`≡ a_p (mod p)`?

Yes: this follows from the greedy-matching reduction of Chojecki [Ch26] combined with an
unconditional Fourier-analytic proof of the required three-prime counting estimate.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/linrock/math-proofs/blob/54f272582dd71321ab9d458663d675edd3d0a463/erdos-689/Solution.lean#L18"]
theorem erdos_689 :
    answer(True) ↔ ∀ᶠ n in .atTop, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  sorry

end Erdos689

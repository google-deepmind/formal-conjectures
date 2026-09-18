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
# Erdős Problem 395

*References:*
- [erdosproblems.com/395](https://www.erdosproblems.com/395)
- [Er45] Erdős, P., *On a lemma of Littlewood and Offord*. Bull. Amer. Math. Soc. (1945),
  898--902.
- [CaCa11] Carnielli, Walter and Carolino, Pietro K., *Adjusting a conjecture of Erdős*. Contrib.
  Discrete Math. (2011), 154--159.
- [HJNS24] X. He, T. Juškevičius, B. Narayanan, and S. Spiro, *The Reverse Littlewood-Offord
  problem of Erdős*. arXiv:2408.11034 (2024).
-/

@[expose] public section

namespace Erdos395

/-- The number of sign patterns $\epsilon \in \{-1,1\}^n$ with
$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq r$. -/
noncomputable def signedSumCount {n : ℕ} (z : Fin n → ℂ) (r : ℝ) : ℕ :=
  {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧ ‖∑ i, (ε i : ℂ) * z i‖ ≤ r}.ncard

/--
If $z_1,\ldots,z_n\in \mathbb{C}$ with $\lvert z_i\rvert=1$ then is it true that the probability
that
$$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq \sqrt{2},$$
where $\epsilon_i\in \{-1,1\}$ uniformly at random, is $\gg 1/n$?

A reverse Littlewood-Offord problem. Erdős originally asked this with $\sqrt{2}$ replaced by $1$,
but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$
for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always.

Solved in the affirmative by He, Juškevičius, Narayanan, and Spiro [HJNS24]. The bound of $1/n$
is the best possible, as shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise.

See also [498](https://www.erdosproblems.com/498).
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos395.lean#L4058"]
theorem erdos_395 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ,
    (∀ i, ‖z i‖ = 1) → c / n ≤ (signedSumCount z √2 : ℝ) / 2 ^ n := by
  sorry

/--
Erdős originally asked [erdős_395](https://www.erdosproblems.com/395) with $\sqrt{2}$ replaced by
$1$, but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$
for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always.
-/
@[category research solved, AMS 5 60]
theorem erdos_395.variants.one : answer(False) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) → c / n ≤ (signedSumCount z 1 : ℝ) / 2 ^ n := by
  sorry

/--
The bound of $1/n$ in [erdős_395](https://www.erdosproblems.com/395) is the best possible, as
shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise.
-/
@[category research solved, AMS 5 60]
theorem erdos_395.variants.sharp : ∃ C : ℝ, ∀ n : ℕ, 0 < n → ∃ z : Fin n → ℂ,
    (∀ i, ‖z i‖ = 1) ∧ (signedSumCount z √2 : ℝ) / 2 ^ n ≤ C / n := by
  sorry

end Erdos395

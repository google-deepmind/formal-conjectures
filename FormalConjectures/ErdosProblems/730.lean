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

import FormalConjecturesUtil

/-!
# Erdős Problem 730

*References:*
  - [erdosproblems.com/730](https://www.erdosproblems.com/730)
  - [A129515](https://oeis.org/A129515)
  - [Pr26] Price, L. (with GPT Pro), *Erdős Problem 730*,
    [proof claim](https://www.erdosproblems.com/forum/thread/730/proof-claims#proof-claim-58) (2026).
-/
namespace Erdos730

abbrev S :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}


/--
Are there infinitely many pairs of integers $n < m$ such that $\binom{2n}{n}$
and $\binom{2m}{m}$ have the same set of prime divisors?

The answer is yes: Price [Pr26] (with GPT Pro) proved the stronger statement that for all $x$
there are $\gg x^{1/2}$ many $n \le x$ such that $\binom{2n}{n}$ and $\binom{2n+2}{n+1}$ have
the same set of prime divisors. The linked formal proof (Blair, with Codex and Claude Code)
establishes `S.Infinite` for a verbatim copy of `S`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos730.lean#L44"]
theorem erdos_730 : answer(True) ↔ S.Infinite := by
  sorry

/--
For example, $(87,88)$ and $(607,608)$ are such pairs.
-/
@[category textbook, AMS 11]
theorem erdos_730.variants.explicit_pairs :
    {(87, 88), (607, 608)} ⊆ S := by
  rintro _ (rfl | rfl) <;> exact ⟨by decide, by native_decide⟩

/--
There are examples where $(n, m) ∈ S$ with $m ≠ n + 1$.

(Found by AlphaProof, although it was implicit already in [A129515])
-/
@[category research solved, AMS 11]
theorem erdos_730.variants.delta_ne_one : ∃ (n m : ℕ), (n, m) ∈ S ∧ m ≠ n + 1 := by
  dsimp [S]
  use 10003
  use 10005
  norm_num [Finset.ext_iff, Nat.choose_eq_zero_iff, Nat.centralBinom]
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  intro p hp
  constructor
  all_goals exact fun h' => or_self_iff.1 (hp.dvd_mul.1 (
    h'.trans (by refine' of_decide_eq_true (by constructor : _ = ↑_))))


end Erdos730

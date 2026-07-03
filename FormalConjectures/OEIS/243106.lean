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
# Conjectures associated with A243106

A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.

*References:*
- [A243106](https://oeis.org/A243106)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA243106


open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k


@[category test, AMS 11]
lemma a_one : a 1 = 10 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = -90 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = -1090 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 8910 := by rfl

@[category test, AMS 11]
lemma a_five : a 5 = -91090 := by rfl


/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/243106.wip.lean#L140"]
theorem digits_sum_restricted (b n : ℕ) (hb : b ≥ 5) :
    ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
    sorry

end OeisA243106

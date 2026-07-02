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
# Conjectures associated with a

a: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that
$\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.

The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.

*References:*
- [A282779](https://oeis.org/A282779)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA282779


open Nat Set Classical

/--
a: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that
$\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }



/--
a: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that
$\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.

The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/282779.wip.lean#L104"]
theorem target_theorem_0
  (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
    sorry


@[category test, AMS 11]
lemma a_one : a 1 = 1 := by exact target_theorem_0 3 1 (by decide) (by decide)

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by exact target_theorem_0 3 2 (by decide) (by decide)

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by exact target_theorem_0 3 3 (by decide) (by decide)

@[category test, AMS 11]
lemma a_four : a 4 = 4 := by exact target_theorem_0 3 4 (by decide) (by decide)

@[category test, AMS 11]
lemma a_five : a 5 = 5 := by exact target_theorem_0 3 5 (by decide) (by decide)

end OeisA282779

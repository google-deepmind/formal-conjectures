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
# Erdős Problem 475

*References:*
- [erdosproblems.com/475](https://www.erdosproblems.com/475)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory* (1973).
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

@[expose] public section

namespace Erdos475

/--
A finite set $A\subseteq \mathbb{F}_p$ has a *valid ordering* if the elements of $A$ can be listed
as $a_1,\ldots,a_t$ so that the partial sums $\sum_{1\leq k\leq m}a_k$ are distinct for all
$1\leq m\leq t$.

The empty partial sum is not one of the partial sums compared here. Thus an intermediate or the
total partial sum may be $0$, provided the positive-length partial sums remain pairwise distinct.
-/
abbrev IsValidOrdering {p : ℕ} (A : Finset (ZMod p)) (l : List (ZMod p)) : Prop :=
  l.Nodup ∧ l.toFinset = A ∧
    ∀ m ∈ Finset.Icc 1 l.length, ∀ n ∈ Finset.Icc 1 l.length,
      (l.take m).sum = (l.take n).sum → m = n

/--
Let $p$ be a prime. Given any finite set $A\subseteq \mathbb{F}_p\backslash \{0\}$, is there always
a rearrangement $A=\{a_1,\ldots,a_t\}$ such that all partial sums $\sum_{1\leq k\leq m}a_k$ are
distinct, for all $1\leq m\leq t$?

This is a problem of Graham, who proved it when $t=p-1$. Such an ordering is often called a valid
ordering. It is known for $t\leq 12$ and for $p-3\leq t\leq p-1$, and it is known for all
sufficiently large primes.
-/
@[category research open, AMS 5 11]
theorem erdos_475 : answer(sorry) ↔
    ∀ (p : ℕ), p.Prime → ∀ A : Finset (ZMod p), 0 ∉ A →
      ∃ l : List (ZMod p), IsValidOrdering A l := by
  sorry

end Erdos475

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
# Erdős Problem 467

*References:*
- [erdosproblems.com/467](https://www.erdosproblems.com/467)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980), p. 93.
-/

@[expose] public section

namespace Erdos467

/-- The primes at most $x$. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- The chosen residue classes from $S$ cover $\{n : \ell \le n < x\}$. -/
def Covers (lower x : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, lower ≤ n → n < x → ∃ p ∈ S, Nat.ModEq p n (a p)

/-- A partition of the primes at most $x$ into two nonempty sets, each covering
$\{n : \ell \le n < x\}$ with one chosen residue class per prime. -/
def TwoCover (lower x : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∃ A B : Finset ℕ,
    A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = primesUpTo x ∧
    Covers lower x A a ∧ Covers lower x B a

/--
Prove the following for all large $x$: there is a choice of congruence classes $a_p$ for
all primes $p\leq x$ and a decomposition $\{p\leq x\}=A\sqcup B$ into two non-empty sets
such that, for all $n<x$, there exist some $p\in A$ and $q\in B$ such that
$n\equiv a_p\pmod{p}$ and $n\equiv a_q\pmod{q}$.

The website notes that [ErGr80] omits crucial quantifiers. Here $x$ ranges over natural
numbers and $n$ over positive integers. The version including zero is stated separately.
-/
@[category research open, AMS 11]
theorem erdos_467 : ∃ X : ℕ, ∀ x : ℕ, X ≤ x → TwoCover 1 x := by sorry

/-- The interpretation of Erdős problem 467 in which the interval includes zero. -/
@[category research open, AMS 11]
theorem erdos_467.variants.nonnegative :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → TwoCover 0 x := by sorry

/-- Restricting a covered interval preserves a two-cover. -/
@[category API, AMS 11]
theorem twoCover_restrict_lower {lower lower' x : ℕ}
    (h : TwoCover lower x) (hl : lower ≤ lower') : TwoCover lower' x := by
  obtain ⟨a, A, B, hAne, hBne, hd, hu, hA, hB⟩ := h
  exact ⟨a, A, B, hAne, hBne, hd, hu,
    fun n hn hx => hA n (hl.trans hn) hx,
    fun n hn hx => hB n (hl.trans hn) hx⟩

end Erdos467

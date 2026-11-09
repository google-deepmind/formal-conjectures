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
# Erdős Problem 963

*References:*
- [erdosproblems.com/963](https://www.erdosproblems.com/963)
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189. [PDF](https://www.renyi.hu/~p_erdos/1965-02.pdf)

A set `B` of real numbers is dissociated if all sums over its finite subsets are distinct. This is
`AddDissociated` in Mathlib.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos963

/-- $f(n)$ is the largest $k$ such that every set $A\subset\mathbb{R}$ with $n$ elements has a
dissociated subset with at least $k$ elements. The set of such $k$ contains $0$ (take the empty
subset) and is bounded by $n$, so `sSup` is a true maximum. The set $A$ may contain $0$, which
can never belong to a dissociated set. For $n = 0$ the value is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

/-- If every set of `n` reals has a dissociated subset with at least `k` elements, then
$k \leq f(n)$. -/
@[category API, AMS 5 11]
theorem le_f {n k : ℕ}
    (h : ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)) :
    k ≤ f n := by
  refine le_csSup ⟨n, fun m hm ↦ ?_⟩ h
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans hA.le)

/-- If `A` has `n` elements and all dissociated subsets of `A` have at most `m` elements, then
$f(n) \leq m$. -/
@[category API, AMS 5 11]
theorem f_le {n m : ℕ} (A : Finset ℝ) (hA : A.card = n)
    (h : ∀ B ⊆ A, AddDissociated (B : Set ℝ) → B.card ≤ m) : f n ≤ m := by
  refine csSup_le ⟨0, fun A' _ ↦ ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩⟩ ?_
  intro k hk
  obtain ⟨B, hBA, hkB, hB⟩ := hk A hA
  exact hkB.trans (h B hBA hB)

def erdos_963.parts.i.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a
subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated that is, the sums
$\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Estimate $f(n)$ - in particular, is it true
that $f(n)\geq \lfloor \log_2 n\rfloor$?

This is the first part, a problem of Erdős [Er65, p. 188]. We read "estimate" as an asymptotic
equivalence $f(n)\sim$ `answer n`. The order of magnitude $\log n$ is easy (see
`erdos_963.variants.greedy` and the example $a_i=i$ in [Er65, p. 188]), so the question is the
constant.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_963.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_963.parts.i.answer := by
  sorry

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a
subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated that is, the sums
$\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Estimate $f(n)$ - in particular, is it true
that $f(n)\geq \lfloor \log_2 n\rfloor$?

This is the second part. Erdős [Er65, p. 188] asks whether the bound $\lfloor\log_3 n\rfloor$ can
be improved to $\lfloor\log_2 n\rfloor$. We state it for all $n\geq 1$, with
$\lfloor\log_2 n\rfloor$ written as `Nat.log 2 n`.

As on the problem page, $A$ is any set of reals. [Er65] speaks of "given numbers" and uses the
example $a_i=i$. Allowing negative numbers makes the question harder. A dissociated set never
contains both $x$ and $-x$, and changing signs keeps a set dissociated. So the largest dissociated
subsets of $A$ and of $\{\lvert a\rvert : a\in A,\ a\neq 0\}$ have the same size, and the sets
$\{\pm a : a\in S\}$ (with $0$ added for odd $n$) show that $f(2m)=f(2m+1)$ is the least size of a
largest dissociated subset of a set of $m$ positive reals. Hence this statement asks for
$\lfloor\log_2 m\rfloor+1$ for $m$ positive reals. The question for positive reals with
$\lfloor\log_2\lvert A\rvert\rfloor$, one less, is `erdos_963.variants.positive`; it follows from
this statement.
-/
@[category research open, question, AMS 5 11]
theorem erdos_963.parts.ii : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n ≤ f n := by
  sorry

/--
Erdős noted that the greedy algorithm showed $f(n)\geq \lfloor \log_3 n\rfloor$
[Er65, p. 188].
-/
@[category research solved, AMS 5 11]
theorem erdos_963.variants.greedy (n : ℕ) : Nat.log 3 n ≤ f n := by
  sorry

/--
The second part for sets of positive reals, with $\lfloor\log_2\lvert A\rvert\rfloor$ as in
[Er65, p. 188] and its example $a_i=i$: every set $A$ of positive reals has a dissociated subset
with at least $\lfloor\log_2 \lvert A\rvert\rfloor$ elements.
-/
@[category research open, question, AMS 5 11]
theorem erdos_963.variants.positive :
    ∀ A : Finset ℝ, (∀ a ∈ A, 0 < a) →
      ∃ B ⊆ A, Nat.log 2 A.card ≤ B.card ∧ AddDissociated (B : Set ℝ) := by
  sorry

end Erdos963

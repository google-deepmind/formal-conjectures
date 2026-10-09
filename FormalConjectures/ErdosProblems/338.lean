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
# Erdős Problem 338

*References:*
- [erdosproblems.com/338](https://www.erdosproblems.com/338)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErGr80b] Erdős, P. and Graham, R. L., *On bases with an exact order*. Acta Arith. (1980),
  201-207.
- [HHP07] Hegyvári, Norbert and Hennecart, François and Plagne, Alain, *Answer to a question by
  Burr and Erdős on restricted addition, and related results*. Combin. Probab. Comput. (2007),
  747--756.
- [He05] Hennecart, François, *On the restricted order of asymptotic bases of order two*.
  Ramanujan J. (2005), 123--130.
- [Ke57] Kelly, John B., *Restricted bases*. Amer. J. Math. (1957), 258-264.
- [Pa33] Pall, Gordon, *On Sums of Squares*. Amer. Math. Monthly (1933), 10-18.
- [Sc54] Schinzel, A., *Sur la décomposition des nombres naturels en sommes de nombres
  triangulaires distincts*. Bull. Acad. Polon. Sci. Cl. III. (1954), 409-410.
-/

@[expose] public section

namespace Erdos338

open Filter

/-- `HasOrder A h` means that $A$ is a basis of order $h$: every sufficiently large natural number
is a sum of at most $h$ elements of $A$, with repetition allowed.

The summands form a `Multiset`, so repetition is allowed. Allowing at most $h$ summands makes the
notion independent of whether $0 \in A$. With exactly $h$ summands, as in
`Set.IsAsymptoticAddBasisOfOrder`, this notion is `(insert 0 A).IsAsymptoticAddBasisOfOrder h`. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

/-- `HasRestrictedOrder A t` means that every sufficiently large natural number is a sum of at most
$t$ distinct elements of $A$.

The summands form a `Finset`, so they are distinct. A summand $0$ never helps, so the notion does
not depend on whether $0 \in A$. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/-- The order of $A$: the least $h$ with `HasOrder A h`, or `⊤` if $A$ is not a basis. -/
noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

/-- The restricted order of $A$: the least $t$ with `HasRestrictedOrder A t`, or `⊤` if no such
$t$ exists. -/
noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

/--
The restricted order of a basis $A$ is the least integer $t$ (if it exists) such that every large
integer is the sum of at most $t$ distinct summands from $A$. What are necessary and sufficient
conditions that this exists?

This uses the `answer(sorry)` mechanism. A solution must supply the condition and prove the
equivalence. Whether a condition is a satisfactory answer is up to human judgement.
-/
@[category research open, AMS 11]
theorem erdos_338 :
    let P : Set ℕ → Prop := answer(sorry)
    ∀ A : Set ℕ, (∃ h, HasOrder A h) → ((∃ t, HasRestrictedOrder A t) ↔ P A) := by
  sorry

/--
Can the restricted order of a basis be bounded (when it exists) in terms of the order of the
basis?

`HasOrder A h` only says that the order of $A$ is at most $h$. This gives the same question,
since $f$ can be replaced by its running maximum. Kelly [Ke57] showed that $f(2) = 4$ works, and
Hennecart [He05] showed that $4$ is optimal. Hegyvári, Hennecart and Plagne [HHP07] showed that
any such $f$ has $f(k) \geq 2^{k-2}+k-1$ for $k \geq 3$.
-/
@[category research open, AMS 11]
theorem erdos_338.variants.bounded_by_order :
    answer(sorry) ↔ ∃ f : ℕ → ℕ, ∀ (A : Set ℕ) (h : ℕ), HasOrder A h →
      (∃ t, HasRestrictedOrder A t) → HasRestrictedOrder A (f h) := by
  sorry

/--
What are necessary and sufficient conditions that the restricted order of a basis $A$ is equal to
the order of $A$?

For a basis, `basisOrder A` is finite, so the equality also says that the restricted order exists.
This uses the `answer(sorry)` mechanism, as in `Erdos338.erdos_338`.
-/
@[category research open, AMS 11]
theorem erdos_338.variants.eq_order :
    let P : Set ℕ → Prop := answer(sorry)
    ∀ A : Set ℕ, (∃ h, HasOrder A h) → (restrictedOrder A = basisOrder A ↔ P A) := by
  sorry

/--
Is it true that if $A \setminus F$ is a basis for all finite sets $F$ then $A$ must have a
restricted order?
-/
@[category research open, AMS 11]
theorem erdos_338.variants.basis_after_finite_removal :
    answer(sorry) ↔ ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) →
      ∃ t, HasRestrictedOrder A t := by
  sorry

/--
Is it true that if the sets $A \setminus F$, for all finite sets $F$, are bases of the same order,
then $A$ must have a restricted order?

We read "the same order" literally: every $A \setminus F$ has the same exact order $h$. This is
equivalent to asking that the orders of the sets $A \setminus F$ are bounded. Removing elements can
only raise the order, so if the orders are bounded, their maximum is attained at some $F_0$, and
$A \setminus F_0 \subseteq A$ satisfies the literal hypothesis.
-/
@[category research open, AMS 11]
theorem erdos_338.variants.same_order_after_finite_removal :
    answer(sorry) ↔ ∀ A : Set ℕ,
      (∃ h : ℕ, ∀ F : Set ℕ, F.Finite → basisOrder (A \ F) = (h : ℕ∞)) →
      ∃ t, HasRestrictedOrder A t := by
  sorry

/--
Bateman observed that for $h \geq 3$ the set $A = \{1\} \cup \{x > 0 : h \mid x\}$ is a basis of
order $h$ with no restricted order.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.bateman (h : ℕ) (hh : 3 ≤ h) :
    basisOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) = h ∧
      ¬ ∃ t, HasRestrictedOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) t := by
  sorry

/--
Kelly [Ke57] showed that any basis of order $2$ has restricted order at most $4$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly (A : Set ℕ) (hA : HasOrder A 2) : HasRestrictedOrder A 4 := by
  sorry

/--
Kelly [Ke57] showed that any basis of order $2$ with positive lower density has restricted order
at most $3$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly_lowerDensity (A : Set ℕ) (hA : HasOrder A 2)
    (hd : 0 < A.lowerDensity) : HasRestrictedOrder A 3 := by
  sorry

/--
Kelly [Ke57] conjectured that any basis of order $2$ has restricted order at most $3$.

This was disproved by Hennecart [He05], who constructed a basis of order $2$ with restricted
order $4$.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.kelly_conjecture :
    answer(False) ↔ ∀ A : Set ℕ, HasOrder A 2 → HasRestrictedOrder A 3 := by
  sorry

/--
The set of squares has order $4$ and restricted order $5$ (see [Pa33]).

Here $0$ is a square. The order is $4$ by Lagrange's four-square theorem, and is not $3$ because
no integer $\equiv 7 \pmod 8$ is a sum of three squares.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.squares :
    basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4 ∧
      restrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) = 5 := by
  sorry

/--
The set of triangular numbers has order $3$ and restricted order $3$ (see [Sc54]).

Here $0$ is a triangular number.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.triangular :
    basisOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) = 3 ∧
      restrictedOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) = 3 := by
  sorry

/--
Hegyvári, Hennecart and Plagne [HHP07] showed that for all $k \geq 2$ there exists a basis of
order $k$ which has restricted order at least $2^{k-2}+k-1$.

The basis built in the proof of Theorem 4 of [HHP07] (for $k \geq 3$) has order exactly $k$ and a
finite restricted order, equal to $2^{k-2}+k-1$. The finiteness matters: without it, Bateman's
example `Erdos338.erdos_338.variants.bateman` would already give the bound. For $k = 2$ the bound
is $2$, and $A = \{1\} \cup \{x : 2 \mid x\}$ works.
-/
@[category research solved, AMS 11]
theorem erdos_338.variants.hegyvari_hennecart_plagne :
    ∀ k : ℕ, 2 ≤ k → ∃ A : Set ℕ,
      basisOrder A = k ∧ restrictedOrder A = (2 ^ (k - 2) + k - 1 : ℕ) := by
  sorry

end Erdos338

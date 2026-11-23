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
# Erdős Problem 1160

*References:*
- [erdosproblems.com/1160](https://www.erdosproblems.com/1160)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
- [BNV07] Blackburn, S. R., Neumann, P. M. and Venkataraman, G., *Enumeration of finite groups*.
  Cambridge Tracts in Mathematics 173, Cambridge University Press (2007), xii+281.
- [Pa03] Pantelidakis, I., *On the Number of Non-isomorphic Groups of the Same Order*. DPhil
  thesis, University of Oxford (2003).
-/

@[expose] public section

open Filter

namespace Erdos1160

/-- $g(n)$, the number of groups of order $n$ up to isomorphism: the number of isomorphism
classes of finite groups $G$ with $\lvert G\rvert = n$.

The groups are the objects of `FiniteGrp.{0}`, the category of finite groups in the lowest
universe. Every finite group is isomorphic to one of them. Two objects are in the same class if
`Nonempty (G ≅ H)` (`CategoryTheory.isIsomorphicSetoid`). We take the image of
`{G | Nat.card G = n}` in the quotient by this relation and count it with `Set.ncard`.

For $n\geq 1$ the number of classes is finite, because a group of order $n$ is determined up to
isomorphism by a multiplication table on `Fin n`. So `Set.ncard` is the true count and not the
junk value $0$ of an infinite set. For $n=0$ the set is empty (a group has an identity), so
$g(0)=0$. -/
noncomputable def g (n : ℕ) : ℕ :=
  (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}).ncard

/-- There are no groups of order $0$. -/
@[category test, AMS 20]
theorem g_zero : g 0 = 0 := by
  have h : {G : FiniteGrp.{0} | Nat.card G = 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun G hG ↦ Nat.card_pos.ne' hG
  simp [g, h]

/-- Let $g(n)$ denote the number of groups of order $n$. If $n\leq 2^m$ then
$g(n)\leq g(2^m)$.

This is [Va99, 5.71] and an open problem (Question 22.16) in [BNV07], where its origin could not
be traced. It has been attributed to Erdős, Higman and others. Pantelidakis [Pa03] proved it for
odd $n$ and $m\geq 3619$.

It is a conjecture, not a question. We take $n\geq 1$; for $n=0$ it holds trivially, since
$g(0)=0$. -/
@[category research open, AMS 20]
theorem erdos_1160 : ∀ n m : ℕ, 0 < n → n ≤ 2 ^ m → g n ≤ g (2 ^ m) := by
  sorry

/-- Question 22.18 of [BNV07] suggests the even stronger conjecture
$$\sum_{n<2^m}g(n) \leq g(2^m)$$
for all sufficiently large $m$ (perhaps even as soon as $m\geq 7$).

The sum is over $1\leq n<2^m$. -/
@[category research open, AMS 20]
theorem erdos_1160.variants.sum :
    ∀ᶠ m : ℕ in atTop, ∑ n ∈ Finset.Ico 1 (2 ^ m), g n ≤ g (2 ^ m) := by
  sorry

end Erdos1160

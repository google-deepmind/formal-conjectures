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
# Erdős Problem 530

*Reference:* [erdosproblems.com/530](https://www.erdosproblems.com/530)

Let `ell(N)` be maximal such that every finite set `A ⊂ ℝ` of cardinality `N`
contains a Sidon subset of cardinality `ell(N)`.  The open question formalized
below is the sharper question on the page, namely whether `ell(N) ~ N^(1/2)`.

The page also records the known order `ell(N) = Θ(N^(1/2))`, following the
Komlós-Sulyok-Szemerédi lower bound and the classical upper bound from
`A = {1, ..., N}`.  This is included as a separate solved statement.

The stronger Alon-Erdős covering conjecture from the remarks is included as a
separate open statement.
-/

namespace Erdos530

open Classical Filter Asymptotics

/--
A finite set of reals is Sidon if every solution to `a + b = c + d`
with all four terms in the set is trivial, i.e. the two ordered pairs are
equal up to swapping.
-/
def IsSidonFinset (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄,
    a ∈ S →
      b ∈ S →
        c ∈ S →
          d ∈ S →
            a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- `A` contains a Sidon subset of cardinality exactly `k`. -/
def HasSidonSubsetOfCard (A : Finset ℝ) (k : ℕ) : Prop :=
  ∃ S : Finset ℝ, S ⊆ A ∧ IsSidonFinset S ∧ S.card = k

/--
`k` is a uniform Sidon-subset size at `N`: every finite real set of cardinality
`N` contains a Sidon subset of cardinality exactly `k`.
-/
def UniformSidonSubsetSize (N k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N → HasSidonSubsetOfCard A k

/--
`k` is the value of the extremal function `ell(N)`: it is the greatest
uniform Sidon-subset size for all finite real sets of cardinality `N`.
The extra condition `m ≤ N` records the natural finite-subset upper bound.
-/
def IsEllValue (N k : ℕ) : Prop :=
  IsGreatest {m : ℕ | m ≤ N ∧ UniformSidonSubsetSize N m} k

/--
The extremal function from Erdős problem 530. This searches up to `N`, since
no subset of an `N`-element set can have cardinality greater than `N`.
-/
noncomputable def ell (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (UniformSidonSubsetSize N) N

/-- The known order statement `ell(N) = Θ(sqrt N)`. -/
def SidonSubsetRootOrder : Prop :=
  (fun N : ℕ => (ell N : ℝ)) =Θ[atTop] (fun N : ℕ => Real.sqrt (N : ℝ))

/--
The sharper open question from Erdős problem 530:
`ell(N) ~ N^(1/2)`, written using `Real.sqrt`.
-/
def SidonSubsetRootAsymptotic : Prop :=
  (fun N : ℕ => (ell N : ℝ)) ~[atTop] (fun N : ℕ => Real.sqrt (N : ℝ))

/--
A formulation independent of the concrete implementation of `ell`: every
function satisfying the maximality specification has the asserted asymptotic.
-/
def SidonSubsetRootAsymptoticForAnyEll : Prop :=
  ∀ ell' : ℕ → ℕ,
    (∀ N : ℕ, IsEllValue N (ell' N)) →
      (fun N : ℕ => (ell' N : ℝ)) ~[atTop] (fun N : ℕ => Real.sqrt (N : ℝ))

/--
`f(N) ≤ (1 + o(1)) g(N)`, phrased as the usual epsilon formulation.
This avoids choosing a particular auxiliary `o(g)` error term.
-/
def EventuallyAtMostOnePlusLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, f N ≤ (1 + ε) * g N

/--
`A` can be written as a union of at most `k` Sidon subsets of `A`.
The Sidon pieces are not required to be disjoint, matching the phrase
"written as the union".
-/
def HasSidonCoverOfCardAtMost (A : Finset ℝ) (k : ℕ) : Prop :=
  ∃ C : Finset (Finset ℝ),
    C.card ≤ k ∧
      (∀ S ∈ C, S ⊆ A ∧ IsSidonFinset S) ∧
        A ⊆ C.biUnion (fun S => S)

/-- `k` Sidon sets always suffice to cover every `N`-element finite real set. -/
def UniformSidonCoverBound (N k : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N → HasSidonCoverOfCardAtMost A k

/--
The stronger Alon-Erdős conjecture mentioned in the remarks: there is a
uniform Sidon-cover bound which is at most `(1 + o(1)) sqrt N`.
-/
def AlonErdosStrongSidonCoverConjecture : Prop :=
  ∃ K : ℕ → ℕ,
    (∀ N : ℕ, UniformSidonCoverBound N (K N)) ∧
      EventuallyAtMostOnePlusLittleO
        (fun N : ℕ => (K N : ℝ))
        (fun N : ℕ => Real.sqrt (N : ℝ))

/--
Let `ell(N)` be maximal such that every finite set `A ⊂ ℝ` of size `N`
contains a Sidon subset of size `ell(N)`.  The remarks on the problem page
record the known order `ell(N) = Θ(N^(1/2))`.
-/
@[category research solved, AMS 11]
theorem erdos_530.parts.i : SidonSubsetRootOrder := by
  sorry

/--
In particular, is it true that `ell(N) ~ N^(1/2)`?
-/
@[category research open, AMS 11]
theorem erdos_530.parts.ii : answer(sorry) ↔ SidonSubsetRootAsymptotic := by

  sorry

/--
Alon and Erdős asked the stronger question of whether every `N`-element finite
set of reals can be written as the union of at most `(1 + o(1)) N^(1/2)` Sidon
sets.
-/
@[category research open, AMS 11]
theorem erdos_530.variants.alon_erdos :
    answer(sorry) ↔ AlonErdosStrongSidonCoverConjecture := by
  sorry

end Erdos530
-- CI: trivial change to trigger lake build

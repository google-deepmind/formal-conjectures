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

import FormalConjecturesUtil

/-!
# Erdős Problem 176

Write $N(k,\ell)$ for the least $N$ such that every $\{-1,1\}$-coloring of
$\{1,\ldots,N\}$ admits a $k$-term arithmetic progression whose sum has
absolute value at least $\ell$. Erdős asks whether $N(k,ck)$, $N(k,2)$ and
$N(k,\sqrt{k})$ are at most exponential in $k$.

Two exact values of $N(k,2)$ are recorded at the end of the file. The choice of
$k$ there is not arbitrary: a $k$-term $\{-1,1\}$ sum has the parity of $k$, so
for even $k$ one has $|s| \geq 1 \iff |s| \geq 2$ and hence
$N(k,2) = N(k,1) = 2^t(k-1)+1$ for $k = 2^t m$ with $m$ odd [Sp73]. The open
content of $N(k,2)$ therefore sits at odd $k$. There $N(3,2) = 9$ is the
classical van der Waerden number $W(2,3)$, and $N(k,2)$ for $k = 5,7,9,11$ was
computed in [Go26]. $k = 13$ and $k = 15$ are the first two beyond that frontier
for which both sides carry exact machine-checkable certificates [Ly26]; for odd
$k \geq 17$ only lower bounds are known, so no further exact value is stated
here.

*References:*
- [erdosproblems.com/176](https://www.erdosproblems.com/176)
- [Sp73] Spencer, J. Solution to Problem P.185.
  Bull. Canad. Math. Soc. 16 (1973), 464.
- [Go26] Goss, M. J., Jr. The Parity Collapse and Entropy Drain: First Bounds
  on Erdős's Discrepancy Threshold N(k,2).
  [Zenodo](https://doi.org/10.5281/zenodo.20763838).
- [Ly26] Lystad, T. A. Erdős Problem 176 — exact small values of the discrepancy
  threshold N(k,2) with machine-checkable DRAT certificates (v1.2: N(15,2) = 225).
  [Zenodo](https://doi.org/10.5281/zenodo.21739846) (concept DOI; resolves to the
  latest version).
-/

open Set ENat

namespace Erdos176

/--
Every coloring of $\{1,\ldots,N\}$ by $\{-1,1\}$ has a $k$-term arithmetic
progression on which the absolute value of the sum is at least $\ell$.

`Set.IsAPOfLength` requires the progression to have exactly $k$ elements, so a
constant progression (common difference zero) does not qualify unless $k = 1$.

This predicate is monotone in $N$: restricting a coloring of $\{1,\ldots,N\}$ to
$\{1,\ldots,N'\}$ for $N' \leq N$ leaves every progression of the smaller
interval, and its sum, unchanged. So `ForcesDiscrepancy · k ℓ` cuts out an
upward-closed set of naturals, and a single coloring avoiding discrepancy $\ell$
on $\{1,\ldots,N\}$ rules out every $N' \leq N$ at once. (Context for reading the
values below; it is not proved in this file.)
-/
def ForcesDiscrepancy (N k : ℕ) (ℓ : ℝ) : Prop :=
  ∀ f : Finset.Icc 1 N → ℤ, (∀ n, f n = -1 ∨ f n = 1) →
    ∃ P : Finset (Finset.Icc 1 N),
      ({(n : ℕ) | n ∈ P} : Set ℕ).IsAPOfLength k ∧
        ℓ ≤ |((∑ n ∈ P, f n : ℤ) : ℝ)|

/--
The least $N$ such that every $\{-1,1\}$-coloring of $\{1,\ldots,N\}$
forces discrepancy at least $\ell$ on a $k$-term arithmetic progression.
The value is `⊤` if no finite such $N$ exists.

Because `ForcesDiscrepancy` is monotone in $N$ the set is upward closed, so the
value is a threshold rather than merely a smallest witness: every $N$ at or above
it forces discrepancy $\ell$, and no $N$ below it does.

A $k$-term $\{-1,1\}$ sum has absolute value at most $k$, so the value is `⊤`
whenever $\ell > k$. In particular `discrepancyAPNumber k 2 = ⊤` for $k \leq 1$.
-/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ∞ :=
  sInf ((fun N : ℕ ↦ (N : ℕ∞)) '' {N : ℕ | ForcesDiscrepancy N k ℓ})

/--
For every meaningful proportional threshold $0 < c \leq 1$, is
$N(k,ck)$ at most exponential in $k$?

The source says "for any $c>0$". Values $c>1$ are impossible because a
$k$-term $\{-1,1\}$ sum has absolute value at most $k$, so the statement
records the nontrivial range and retains the boundary case $c=1$.
-/
@[category research open, AMS 5]
theorem erdos_176.parts.i : answer(sorry) ↔
    ∀ c : ℝ, 0 < c → c ≤ 1 → ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k (c * k) ≤ (C ^ k : ℕ) := by
  sorry

/--
Is $N(k,2)$ at most exponential in $k$?

The hypothesis $2 \leq k$, which all three parts carry, is what rules out the
degenerate lengths, and this is the part where it is load-bearing:
`discrepancyAPNumber k 2 = ⊤` for $k \leq 1$, so without it no $C$ could work
and the statement would be false for reasons that have nothing to do with the
question. In parts (i) and (iii) the threshold at $k \leq 1$ is met by a single
term, so there the hypothesis only keeps the three statements uniform.
-/
@[category research open, AMS 5]
theorem erdos_176.parts.ii : answer(sorry) ↔
    ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k 2 ≤ (C ^ k : ℕ) := by
  sorry

/-- Is $N(k,\sqrt{k})$ at most exponential in $k$? -/
@[category research open, AMS 5]
theorem erdos_176.parts.iii : answer(sorry) ↔
    ∃ C : ℕ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
      discrepancyAPNumber k (Real.sqrt k) ≤ (C ^ k : ℕ) := by
  sorry

/--
$N(13,2)=158$: there is an avoiding coloring at $N=157$, while the
$N=158$ instance is unsatisfiable. Both sides have exact machine-checkable
certificates in [Ly26].

The coloring at $N=157$ settles every smaller case as well: restricted to
$\{1,\ldots,N'\}$ for $N' \leq 157$ it still avoids, so no $N' \leq 157$ lies in
the set and $158$, which does, is its least element.
-/
@[category research solved, AMS 5]
theorem erdos_176.variants.n_13_two : discrepancyAPNumber 13 2 = 158 := by
  sorry

/--
$N(15,2)=225$: there is an avoiding coloring at $N=224$, while the
$N=225$ instance is unsatisfiable. Both sides have exact machine-checkable
certificates in [Ly26].

As above, the coloring at $N=224$ restricts to every $N' \leq 224$, so $225$ is
the least element of the set rather than merely a member of it.
-/
@[category research solved, AMS 5]
theorem erdos_176.variants.n_15_two : discrepancyAPNumber 15 2 = 225 := by
  sorry

end Erdos176

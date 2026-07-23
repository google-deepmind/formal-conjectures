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
# Erdős Problem 959

*Reference:* [erdosproblems.com/959](https://www.erdosproblems.com/959)
-/

namespace Erdos959

open Filter
open scoped Topology

noncomputable section

/-- A point of the real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance. Squaring is injective on nonnegative reals, so
equality of `sqDist` is equivalent to equality of ordinary Euclidean distance,
and the two determine the same distance classes and multiplicities. -/
def sqDist (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The unordered index pairs, represented uniquely by the orientation `i < j`. -/
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

/-- The finite set of distinct squared distances determined by a configuration. -/
def distanceValues {n : ℕ} (P : Fin n → Point) : Finset ℝ :=
  (indexPairs n).image fun ij => sqDist (P ij.1) (P ij.2)

/-- `f(d)`: the number of unordered pairs in `P` determining squared distance `d`. -/
def frequency {n : ℕ} (P : Fin n → Point) (d : ℝ) : ℕ :=
  ((indexPairs n).filter fun ij => sqDist (P ij.1) (P ij.2) = d).card

/-- For a fixed distance `d`, the largest multiplicity among all *other*
represented distances (`Finset.sup` returns `0` when there is no other value). -/
def runnerUpFrequency {n : ℕ} (P : Fin n → Point) (d : ℝ) : ℕ :=
  ((distanceValues P).erase d).sup (frequency P)

/-- `f(d₁) - f(d₂)`: the gap between the largest and second-largest distance
multiplicities. The supremum over `d` handles both a unique winner and a tie:
non-winners contribute `0` by truncated subtraction, and tied winners also
contribute `0`. -/
def multiplicityGap {n : ℕ} (P : Fin n → Point) : ℕ :=
  (distanceValues P).sup fun d => frequency P d - runnerUpFrequency P d

/-- A configuration represents a set of size `n` (injective) and has at least
two distinct distances, so that `d₂` exists. -/
def Admissible {n : ℕ} (P : Fin n → Point) : Prop :=
  Function.Injective P ∧ 2 ≤ (distanceValues P).card

/-- A natural number occurs as the top-two multiplicity gap of some admissible
`n`-point configuration. -/
def AttainableGap (n g : ℕ) : Prop :=
  ∃ P : Fin n → Point, Admissible P ∧ multiplicityGap P = g

/-- The extremal quantity of the problem, `max_{|A| = n} (f(d₁) - f(d₂))`. There
are `Nat.choose n 2` unordered pairs, so this is a valid finite search interval. -/
def extremalGap (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (AttainableGap n) (Nat.choose n 2)

/--
Let $A\subseteq \mathbb{R}^2$ be a set of size $n$ and let $\{d_1,\ldots,d_k\}$ be
the set of distinct distances determined by $A$. Let $f(d)$ be the number of times
the distance $d$ is determined, ordered so that
$f(d_1)\geq f(d_2)\geq \cdots \geq f(d_k)$. Estimate
$$\max (f(d_1)-f(d_2)),$$
where the maximum is taken over all $A$ of size $n$ (this is `extremalGap n`).

The asymptotic order of `extremalGap` is not known; a natural formalization of
"estimate" asks whether it has a well-defined polynomial growth exponent.
-/
@[category research open, AMS 52]
theorem erdos_959 : answer(sorry) ↔
    ∃ γ : ℝ, Tendsto (fun n : ℕ => Real.log (extremalGap n) / Real.log n) atTop (𝓝 γ) := by
  sorry

/--
A superlinear lower bound: there is a `c > 0` such that for all large `n`,
`extremalGap n ≥ n^{1 + c / log log n}`. In particular `max (f(d₁) - f(d₂))` grows
faster than any linear function of `n`. This is a proved lower bound; determining
the exact order of `extremalGap` remains open (see `erdos_959`).
-/
@[category research solved, AMS 52, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-959/Research/FinalLowerBound.lean"]
theorem erdos_959.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ) ^ (1 + c / Real.log (Real.log n)) ≤ extremalGap n := by
  sorry

end

end Erdos959

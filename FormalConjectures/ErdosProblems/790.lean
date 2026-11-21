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
# Erdős Problem 790

*References:*
- [erdosproblems.com/790](https://www.erdosproblems.com/790)
- [Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math.
  8 (1965), 181–189, p. 188.
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_.
  A Survey of Combinatorial Theory (1973), 117–138, p. 130.
- [CKS75] Choi, S. L. G., Komlós, J. and Szemerédi, E., _On sum-free subsequences_.
  Trans. Amer. Math. Soc. 212 (1975), 307–313.
  [DOI](https://doi.org/10.1090/S0002-9947-1975-0376594-1).
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace Erdos790


/-- No element equals a sum of two or more distinct other elements.
All integers, including zero, are allowed. -/
def DistinctSubsetSumFree (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ S : Finset ℤ,
    S ⊆ B.erase a → 2 ≤ S.card → (∑ x ∈ S, x) ≠ a

def Guarantees (n k : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.card = n →
    ∃ B ⊆ A, DistinctSubsetSumFree B ∧ k ≤ B.card

noncomputable def l (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) n

def erdos_790.parts.i.answer : ℕ → ℝ := by sorry

/-- Let $l(n)$ be maximal such that if $A\subset\mathbb{Z}$ with $\lvert A\rvert=n$
then there exists a sum-free $B\subseteq A$ with $\lvert B\rvert \geq l(n)$ - that is,
$B$ is such that there are no solutions to $a_1=a_2+\cdots+a_r$
with $a_i\in B$ all distinct.
Estimate $l(n)$.

This is interpreted as asking for the order of growth of $l(n)$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_790.parts.i :
    (fun n ↦ (l n : ℝ)) =Θ[atTop] erdos_790.parts.i.answer := by sorry

/-- In particular, is it true that $l(n)n^{-1/2}\to\infty$? The lower bound in [CKS75,
Theorem (1.1)] gives a positive answer.
-/
@[category research solved, question, AMS 5 11]
theorem erdos_790.parts.ii :
    Tendsto (fun n : ℕ ↦ (l n : ℝ) / Real.sqrt (n : ℝ)) atTop atTop := by sorry

/-- Is it true that $l(n)<n^{1-c}$ for some $c>0$?
The inequality is interpreted as holding for all sufficiently large $n$.
-/
@[category research open, question, AMS 5 11]
theorem erdos_790.parts.iii :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (l n : ℝ) < (n : ℝ) ^ (1 - c) := by sorry

/-- Choi, Komlós and Szemerédi [CKS75, Theorem (1.1)] proved
$\sqrt{n\log n/\log\log n}\ll l(n)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_790.variants.lower_bound :
    (fun n : ℕ ↦ Real.sqrt ((n : ℝ) * Real.log n / Real.log (Real.log n)))
      =O[atTop] (fun n ↦ (l n : ℝ)) := by sorry

/-- Choi, Komlós and Szemerédi [CKS75, Theorem (1.1)] proved
$l(n)\ll n/\log n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_790.variants.upper_bound :
    (fun n ↦ (l n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) / Real.log n) := by sorry

/-- Choi, Komlós and Szemerédi suggest in the closing paragraph of [CKS75]
that $l(n)\geq n^{1-o(1)}$.
-/
@[category research open, AMS 5 11]
theorem erdos_790.variants.near_linear :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - ε) ≤ (l n : ℝ) := by sorry

end Erdos790


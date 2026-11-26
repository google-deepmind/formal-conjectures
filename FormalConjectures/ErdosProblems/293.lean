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
# Erdős Problem 293

*References:*
- [erdosproblems.com/293](https://www.erdosproblems.com/293)
- Wouter van Doorn and Quanyu Tang, *The smallest denominator not contained in a unit fraction
  decomposition of 1 with fixed length*, [arXiv:2512.22083v2](https://arxiv.org/abs/2512.22083v2).
-/

@[expose] public section

namespace Erdos293

/-- Ordered, positive, distinct denominators, exactly $k$ terms, with reciprocal sum $1$. -/
def Decomposition (k : ℕ) (ns : List ℕ) : Prop :=
  ns.length = k ∧
  (∀ n ∈ ns, 1 ≤ n) ∧
  ns.Pairwise (fun a b => a < b) ∧
  (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = 1

/-- The denominator $m$ occurs in a $k$-term decomposition. The tuple may depend on $m$. -/
def Occurs (k m : ℕ) : Prop :=
  ∃ ns : List ℕ, Decomposition k ns ∧ m ∈ ns

/-- Relational specification of $m = v(k)$, with the essential restriction $m > 1$.
This does not assert existence for arbitrary $k$. -/
def IsFirstMissing (k m : ℕ) : Prop :=
  1 < m ∧ ¬ Occurs k m ∧
  ∀ j : ℕ, 1 < j → j < m → Occurs k j

/-- Statement of van Doorn–Tang, Theorem 1.1: $v(k) \geq e^{ck^2}$ for a uniform $c > 0$.
Existence of the minimum is included explicitly. This definition supplies no proof. -/
def VanDoornTangLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
    ∃ m : ℕ, IsFirstMissing k m ∧
      Real.exp (c * (k : ℝ)^2) ≤ (m : ℝ)

/-- One eventual interpretation of the stronger speculation: $v(k) \geq e^{e^{ck}}$.
This is a statement only. The source does not select a unique growth target. -/
def DoubleExponentialLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ k : ℕ, K ≤ k → ∃ m : ℕ, IsFirstMissing k m ∧
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (m : ℝ)

/-- Uniqueness of the relationally specified minimum; not its existence. -/
@[category API, AMS 11]
theorem firstMissing_unique {k a b : ℕ}
    (ha : IsFirstMissing k a) (hb : IsFirstMissing k b) : a = b := by
  rcases ha with ⟨ha1, haNot, haBefore⟩
  rcases hb with ⟨hb1, hbNot, hbBefore⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (haNot (hbBefore a ha1 hab))
  · exact hab
  · exact False.elim (hbNot (haBefore b hb1 hab))

/-- A single decomposition containing $13856992$. -/
def certificate13856992 : List ℕ :=
  [2, 3, 7, 65, 119, 46566, 13856992, 53675814688, 6273641486385]

/-- A proposed certificate containing $681943$, sorted in increasing order. -/
def certificate681943 : List ℕ :=
  [2, 3, 7, 144, 1984, 15498, 681943, 16608039822, 155008371672]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The certificate containing $13856992$ is a nine-term decomposition of $1$. -/
@[category test, AMS 11]
theorem certificate13856992_valid : Decomposition 9 certificate13856992 := by
  norm_num [Decomposition, certificate13856992, List.pairwise_cons]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The proposed certificate containing $681943$ is not a decomposition of $1$. -/
@[category test, AMS 11]
theorem certificate681943_invalid : ¬ Decomposition 9 certificate681943 := by
  norm_num [Decomposition, certificate681943, List.pairwise_cons]

/-- The denominator $13856992$ occurs in a nine-term decomposition of $1$. -/
@[category test, AMS 11]
theorem occurs13856992 : Occurs 9 13856992 := by
  exact ⟨certificate13856992, certificate13856992_valid, by decide⟩

/-- The proposed certificate containing $681943$ has reciprocal sum $1 - 131225/8053056$. -/
@[category test, AMS 11]
theorem certificate681943_sum :
    (certificate681943.map (fun n => (1 : ℚ) / (n : ℚ))).sum =
      1 - (131225 : ℚ) / 8053056 := by
  norm_num [certificate681943]

end Erdos293

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
# Erdős Problem 1114

*References:*
- [erdosproblems.com/1114](https://www.erdosproblems.com/1114)
- [Ba60b] Bálint, E., *Über die Nullstellen der Ableitung von Polynomen mit lauter reellen
  Nullstellen*. Acta Math. Acad. Sci. Hungar. (1960), 137-140.
-/

open Polynomial Set

namespace Erdos1114

/-- The ordered list of roots of a univariate polynomial, counted without multiplicity. -/
noncomputable def orderedRoots (f : ℝ[X]) : List ℝ :=
  (f.roots.toFinset.sort (· ≤ ·))

/-- Consecutive gaps of a strictly sorted list. -/
def consecutiveGaps : List ℝ → List ℝ
  | a :: b :: rest => (b - a) :: consecutiveGaps (b :: rest)
  | _ => []

/--
Let $f(x)\in \mathbb{R}[x]$ be a polynomial of degree $n$ whose roots $\{a_0<\cdots<a_n\}$ are all
real and form an arithmetic progression. The differences between consecutive zeros of $f'(x)$,
beginning from the midpoint of $(a_0,a_n)$ towards the endpoints, are monotonically increasing.

Proved by Bálint [Ba60b].
-/
@[category research solved, AMS 26 30]
theorem erdos_1114 (f : ℝ[X]) (hf : f.natDegree ≥ 2)
    (hroots : f.roots.toFinset.card = f.natDegree + 1)
    (hAP : ∃ a d : ℝ, d > 0 ∧
      f.roots.toFinset = Finset.image (fun i : ℕ ↦ a + i * d) (Finset.range (f.natDegree + 1))) :
    let as := orderedRoots f
    let bs := orderedRoots f.derivative
    let mid : ℝ := ((as.headI + as.getLastI) / 2)
    let right := bs.filter (fun x ↦ mid ≤ x)
    let left := (bs.filter (fun x ↦ x ≤ mid)).reverse
    (consecutiveGaps right).Pairwise (· ≤ ·) ∧ (consecutiveGaps left).Pairwise (· ≤ ·) := by
  sorry

end Erdos1114

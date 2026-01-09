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
# Erdős Problem 1105

The anti-Ramsey number AR(n, G) is the maximum possible number of colours in which the edges of
Kₙ can be coloured without creating a rainbow copy of G (i.e. one in which all edges have
different colours).

## Conjecture for Cycles

Let Cₖ be the cycle on k vertices. Is it true that
  AR(n, Cₖ) = ((k-2)/2 + 1/(k-1)) n + O(1)?

## Conjecture for Paths

Let Pₖ be the path on k vertices and ℓ = ⌊(k-1)/2⌋. If n ≥ k ≥ 5 then is AR(n, Pₖ) equal to
  max(C(k-2, 2) + 1, C(ℓ-1, 2) + (ℓ-1)(n-ℓ+1) + ε)
where ε = 1 if k is odd and ε = 2 otherwise?

A conjecture of Erdős, Simonovits, and Sós [ESS75], who gave a simple proof that AR(n, C₃) = n-1.
Simonovits and Sós [SiSo84] published a proof that the claimed formula for AR(n, Pₖ) is true
for n ≥ ck² for some constant c > 0.
A proof of the formula for AR(n, Pₖ) for all n ≥ k ≥ 5 has been announced by Yuan [Yu21].

*Reference:* [erdosproblems.com/1105](https://www.erdosproblems.com/1105)
-/

namespace Erdos1105

open SimpleGraph

/-- The path graph on `k` vertices: vertices are `Fin k` and vertex `i` is adjacent to `i+1`. -/
def pathGraph (k : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => i.val + 1 = j.val

/-- An edge coloring of a simple graph `G` with color type `α`. -/
def EdgeColoring (G : SimpleGraph V) (α : Type*) := G.edgeSet → α

/-- A subgraph `H` of a graph with edge coloring `c` is rainbow if all edges of `H` have distinct
colors. -/
def IsRainbow {V : Type*} {G : SimpleGraph V} (c : EdgeColoring G α) (H : G.Subgraph) : Prop :=
  Function.Injective fun e : H.edgeSet => c ⟨e.val, H.edgeSet_subset e.property⟩

/-- A graph `G` contains a rainbow copy of `H` if there is a subgraph of `G` that is isomorphic
to `H` and is rainbow under the edge coloring `c`. -/
def HasRainbowCopy {V W : Type*} {G : SimpleGraph V} (c : EdgeColoring G α) (H : SimpleGraph W) :
    Prop :=
  ∃ (S : G.Subgraph), H ⊑ S.coe ∧ IsRainbow c S

/-- An edge coloring of `Kₙ` with `m` colors that avoids rainbow copies of `H`. -/
def IsAntiRamseyColoring (n m : ℕ) (H : SimpleGraph W) : Prop :=
  ∃ (c : EdgeColoring (completeGraph (Fin n)) (Fin m)), ¬HasRainbowCopy c H

/-- The anti-Ramsey number AR(n, H) is the maximum number of colors in which the edges of Kₙ
can be colored without creating a rainbow copy of H. -/
noncomputable def antiRamseyNumber (n : ℕ) (H : SimpleGraph W) : ℕ :=
  sSup {m : ℕ | IsAntiRamseyColoring n m H}

/-- The conjectured value for the anti-Ramsey number of cycles.
  AR(n, Cₖ) ≈ ((k-2)/2 + 1/(k-1)) · n -/
noncomputable def conjecturedARCycle (n k : ℕ) : ℝ :=
  ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n

/-- The conjectured value for the anti-Ramsey number of paths.
  AR(n, Pₖ) = max(C(k-2, 2) + 1, C(ℓ-1, 2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋ and ε = 1 if k is odd, ε = 2 otherwise. -/
noncomputable def conjecturedARPath (n k : ℕ) : ℕ :=
  let ell := (k - 1) / 2  -- ℓ = ⌊(k-1)/2⌋
  let eps := if k % 2 = 1 then 1 else 2  -- ε = 1 if k odd, 2 otherwise
  max (Nat.choose (k - 2) 2 + 1)
      (Nat.choose (ell - 1) 2 + (ell - 1) * (n - ell + 1) + eps)

/--
The anti-Ramsey number for cycles satisfies
  AR(n, Cₖ) = ((k-2)/2 + 1/(k-1)) · n + O(1).
This is a conjecture of Erdős, Simonovits, and Sós [ESS75].
-/
@[category research open, AMS 5]
theorem erdos_1105_cycles (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ, |antiRamseyNumber n (cycleGraph k) - conjecturedARCycle n k| ≤ C := by
  sorry

/--
The anti-Ramsey number for paths satisfies
  AR(n, Pₖ) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋ and ε = 1 if k is odd and ε = 2 otherwise.
This is a conjecture of Erdős, Simonovits, and Sós [ESS75].
The case n ≥ k ≥ 5 has been announced as proven by Yuan [Yu21].
-/
@[category research open, AMS 5]
theorem erdos_1105.variants.paths (n k : ℕ) (hn : k ≤ n) (hk : 5 ≤ k) :
    antiRamseyNumber n (pathGraph k) = conjecturedARPath n k := by
  sorry

/--
Known result: AR(n, C₃) = n - 1.
Proved by Erdős, Simonovits, and Sós [ESS75].
-/
@[category research solved, AMS 5]
theorem erdos_1105.variants.triangles (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNumber n (cycleGraph 3) = n - 1 := by
  sorry

end Erdos1105



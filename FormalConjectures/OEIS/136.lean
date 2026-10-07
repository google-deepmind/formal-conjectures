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
# Stamp folding

The number of distinct ways to fold a strip of $n$ labeled stamps into a flat pile.
A permutation $\sigma$ of $\{0, \ldots, n-1\}$ represents a valid stamp folding if the
connections between consecutive stamps do not cross in the folded stack: for all
$0 \le i < j \le n-2$, the intervals
$[\min(\sigma(i), \sigma(i+1)), \max(\sigma(i), \sigma(i+1))]$ and
$[\min(\sigma(j), \sigma(j+1)), \max(\sigma(j), \sigma(j+1))]$ are either disjoint or nested.

*References:*
- [A000136](https://oeis.org/A000136)
- [Map Folding](https://mathworld.wolfram.com/MapFolding.html)
- [Stamp Folding](https://mathworld.wolfram.com/StampFolding.html)
- [Map folding (Wikipedia)](https://en.wikipedia.org/wiki/Map_folding)
-/

@[expose] public section

namespace OeisA136

/-- Two intervals $[\min(a,b), \max(a,b)]$ and $[\min(c,d), \max(c,d)]$ cross,
i.e., they interleave without nesting. -/
def IntervalsCross (a b c d : ℕ) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

instance {a b c d : ℕ} : Decidable (IntervalsCross a b c d) := by
  unfold IntervalsCross; infer_instance

/-- A permutation $\sigma$ of $\{0, \ldots, n-1\}$ is a valid stamp folding if no two
connections between consecutive stamps in the original strip cross in the stack ordering.
Connection $i$ links the stack positions $\sigma(i)$ and $\sigma(i+1)$ of consecutive
stamps $i$ and $i+1$. -/
def IsStampFolding {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i j : Fin (n - 1)), i < j →
    ¬IntervalsCross
      (σ ⟨i.val, by omega⟩).val (σ ⟨i.val + 1, by omega⟩).val
      (σ ⟨j.val, by omega⟩).val (σ ⟨j.val + 1, by omega⟩).val

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsStampFolding σ) := by
  unfold IsStampFolding; infer_instance

/-- Number of distinct stamp foldings of a strip of $n$ labeled stamps (OEIS A000136). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsStampFolding σ).card

@[category test, AMS 5]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 5]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 5]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 5]
theorem a_4 : a 4 = 16 := by decide

@[category test, AMS 5]
theorem a_5 : a 5 = 50 := by decide

/--
"Determine the precise limiting ratio $\lim_{n \to \infty} \frac{a_{n+1}}{a_n}$."
The limit is known to exist and lie in the interval $[3.3868, 3.9821]$, but its exact value
is unknown. It is unclear whether the limit has a closed form or is transcendental.

*References:*
- [A000136](https://oeis.org/A000136)
- [Map Folding](https://mathworld.wolfram.com/MapFolding.html)
-/
@[category research open, AMS 5 40]
theorem growth_rate :
    let L : ℝ := answer(sorry)
    3.3868 ≤ L ∧ L ≤ 3.9821 ∧
      Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ))
        Filter.atTop (nhds L) := by
  sorry

end OeisA136

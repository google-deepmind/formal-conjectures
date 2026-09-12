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
# Erdős Problem 1160

*References:*
- [erdosproblems.com/1160](https://www.erdosproblems.com/1160)
- [BNV07] Blackburn, Simon R. and Neumann, Peter M. and Venkataraman,
  Geetha, *Enumeration of finite groups*. (2007), xii+281.
- [Pa03] I. Pantelidakis, *On the Number of Non-isomorphic Groups of the Same Order*.
  DPhil Thesis, University of Oxford (2003).
-/

namespace Erdos1160

/-- Two group structures on the same carrier are isomorphic. -/
def isomorphic {α : Type*} (G H : Group α) : Prop :=
  Nonempty (@MulEquiv α α G.toMul H.toMul)

/--
$g(n)$ is the number of groups of order $n$ up to isomorphism.

Every group of order $n$ is isomorphic to a group structure on `Fin n`.
-/
noncomputable def g (n : ℕ) : ℕ :=
  Nat.card (Quot (α := Group (Fin n)) isomorphic)

/--
Let $g(n)$ denote the number of groups of order $n$. If $n\leq 2^m$ then $g(n)\leq g(2^m)$.
-/
@[category research open, AMS 20]
theorem erdos_1160 (n m : ℕ) (h : n ≤ 2 ^ m) : g n ≤ g (2 ^ m) := by
  sorry

/--
Question 22.18 of [BNV07] suggests the even stronger conjecture
$$\sum_{n<2^m}g(n) \leq g(2^m)$$
for all sufficiently large $m$ (perhaps even as soon as $m\geq 7$).
-/
@[category research open, AMS 20]
theorem erdos_1160.variants.sum :
    ∃ M, ∀ m ≥ M, ∑ n ∈ Finset.range (2 ^ m), g n ≤ g (2 ^ m) := by
  sorry

/--
Pantelidakis [Pa03] proved that the original conjecture is true if $n$ is odd and $m\geq 3619$.
-/
@[category research solved, AMS 20]
theorem erdos_1160.variants.odd {n m : ℕ} (hn : Odd n) (hm : 3619 ≤ m) (hle : n ≤ 2 ^ m) :
    g n ≤ g (2 ^ m) := by
  sorry

end Erdos1160

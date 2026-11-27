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
# Erdős Problem 1016

*References:*
- [erdosproblems.com/1016](https://www.erdosproblems.com/1016)
- [Bo71] J. A. Bondy, *Pancyclic graphs I*, J. Combin. Theory Ser. B 11 (1971), 80–84.
- [Gr13] S. Griffin, *Minimal pancyclicity*,
  [arXiv:1312.0274](https://arxiv.org/abs/1312.0274) (2013).
- [GKW16] J. C. George, A. Khodkar and W. D. Wallis, *Pancyclic and bipancyclic graphs*,
  SpringerBriefs in Mathematics (2016), Chapter 4.5.
-/

@[expose] public section

open Filter

namespace Erdos1016

/-- A graph on a finite vertex type is pancyclic if it contains a cycle of length $k$ for every
$3 \le k \le \lvert V\rvert$. -/
def IsPancyclic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ k, 3 ≤ k → k ≤ Fintype.card V → ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = k

/-- The minimum number of edges of a pancyclic graph on $n$ vertices. -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {e | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ G.edgeSet.ncard = e}

/-- $h(n) = m(n) - n$: a pancyclic graph on $n$ vertices has $n + h(n)$ edges at the minimum. -/
noncomputable def h (n : ℕ) : ℤ := (m n : ℤ) - n

/-- Every graph on at most two vertices is pancyclic, since there is no length to check. So `m n`
is the junk value $0$ for $n \le 2$, and the statements below assume $n \ge 3$. -/
@[category test, AMS 5]
theorem isPancyclic_of_card_le_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 2) : IsPancyclic G := by
  intro k hk hkV
  omega

/--
Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n + h(n)$ edges which
contains a cycle on $k$ vertices for every $3 \le k \le n$. Is it true that
$$h(n) \ge \log_2 n + \log_* n - O(1)?$$

Here $\log_*$ is `Nat.iteratedLog 2`. Other choices of base change $\log_* n$ by $O(1)$.
-/
@[category research open, question, AMS 5]
theorem erdos_1016 :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Real.logb 2 n + Nat.iteratedLog 2 n - C ≤ h n := by
  sorry

/--
Bondy [Bo71] stated without proof, and Griffin [Gr13] proved, the lower bound
$h(n) \ge \log_2(n - 1) - 1$.
-/
@[category research solved, AMS 5]
theorem erdos_1016.variants.lower (n : ℕ) (hn : 3 ≤ n) :
    Real.logb 2 (n - 1) - 1 ≤ h n := by
  sorry

/--
Bondy [Bo71] stated without proof the upper bound $h(n) \le \log_2 n + \log_* n + O(1)$. The first
published proof is in George, Khodkar and Wallis [GKW16, Chapter 4.5].
-/
@[category research solved, AMS 5]
theorem erdos_1016.variants.upper :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (h n : ℝ) ≤ Real.logb 2 n + Nat.iteratedLog 2 n + C := by
  sorry

end Erdos1016

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
# Erdős Problem 543

*Reference:* [erdosproblems.com/543](https://www.erdosproblems.com/543)

Define $f(N)$ as the minimal $k$ such that a random $k$-element subset of an abelian group
of order $N$ is subset-sum complete with probability $\geq 1/2$. Erdős and Rényi proved
$f(N) \leq \log_2 N + O(\log \log N)$. This problem asks whether the bound can be improved
to $f(N) \leq \log_2 N + o(\log \log N)$. Disproved by ChatGPT and Tang.

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
(1973), 117-138.

[ErHa78b] Erdős, P. and Hajnal, A., 1978.
-/

open Finset Filter Classical

open scoped BigOperators

namespace Erdos543

/-- A subset $A$ of an additive commutative group is subset-sum complete if every
element of the group can be expressed as a sum over some subset of $A$. -/
def SubsetSumComplete {G : Type*} [AddCommGroup G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ ∑ x ∈ S, x = g

/-- The number of $k$-element subsets of $\mathbb{Z}/n\mathbb{Z}$ that are subset-sum complete.
Returns $0$ when $n = 0$ (since $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$ is not finite). -/
noncomputable def sscCountMod (n k : ℕ) : ℕ :=
  if h : n = 0 then 0
  else by
    haveI : NeZero n := ⟨h⟩
    exact ((Finset.univ : Finset (ZMod n)).powersetCard k).filter
      (fun A => SubsetSumComplete A) |>.card

/-- The total number of $k$-element subsets of $\mathbb{Z}/n\mathbb{Z}$.
Returns $0$ when $n = 0$. -/
noncomputable def totalSubsetsMod (n k : ℕ) : ℕ :=
  if h : n = 0 then 0
  else by
    haveI : NeZero n := ⟨h⟩
    exact ((Finset.univ : Finset (ZMod n)).powersetCard k).card

/--
Erdős Problem 543 (disproved):

Define $f(N)$ as the minimal $k$ such that for every abelian group $G$ of size $N$,
a uniformly random subset $A \subseteq G$ of size $k$ is subset-sum complete with
probability $\geq 1/2$. Erdős and Rényi proved $f(N) \leq \log_2 N + O(\log \log N)$.

The conjecture asked whether $f(N) \leq \log_2 N + o(\log \log N)$. Erdős believed
this improvement is impossible [Er73, p.127], [ErHa78b].

This was confirmed (conjecture disproved) by ChatGPT and Tang. The
formalization states: no function $g = o(\log \log N)$ can improve the bound,
even for cyclic groups $\mathbb{Z}/N\mathbb{Z}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_543 :
    answer(False) ↔
    (∃ g : ℕ → ℝ,
      Tendsto (fun N => g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0) ∧
      ∀ᶠ (N : ℕ) in atTop,
        let k := Nat.ceil (Real.log (↑N : ℝ) / Real.log 2 + g N)
        2 * sscCountMod N k ≥ totalSubsetsMod N k) := by
  sorry

end Erdos543

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
# Erdős Problem 702

*References:*
- [erdosproblems.com/702](https://www.erdosproblems.com/702)
- [Er75f] Erdős, Paul, _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99-108.
- [Er76b] Erdős, P., _Problems and results in graph theory and combinatorial analysis_.
  Proceedings of the Fifth British Combinatorial Conference (Univ. Aberdeen, Aberdeen, 1975)
  (1976), 169-192.
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
- [Fr77] Frankl, Péter, _On families of finite sets no two of which intersect in a singleton_.
  Bull. Austral. Math. Soc. (1977), 125-134.
-/

@[expose] public section

open Filter Finset

namespace Erdos702

/--
Let $k\geq 4$. If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ with $\lvert A\rvert=k$
for all $A\in \mathcal{F}$ and $\lvert \mathcal{F}\rvert >\binom{n-2}{k-2}$ then there are
$A,B\in\mathcal{F}$ such that $\lvert A\cap B\rvert=1$.

A conjecture of Erdős and Sós. Katona (unpublished) proved this when $k=4$, and Frankl [Fr77]
proved this for all $k\geq 4$.

Frankl's theorem is for $n$ sufficiently large in terms of $k$, and this is the form stated here.
Without this assumption the statement is false, see `erdos_702.variants.all_n_false`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos702.lean#L4740"]
theorem erdos_702 (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1 := by
  sorry

/--
The statement does not hold for all $n$. For $k=4$ and $n=5$, the family of all $4$-subsets of
$\{1,\ldots,5\}$ has $5>\binom{3}{2}$ members, and any two of them meet in at least $3$ elements.
-/
@[category textbook, AMS 5]
theorem erdos_702.variants.all_n_false :
    ¬ ∀ k : ℕ, 4 ≤ k → ∀ (n : ℕ) (𝓕 : Finset (Finset (Fin n))), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1 := by
  intro h
  obtain ⟨A, hA, B, hB, hAB⟩ := h 4 le_rfl 5 {A | A.card = 4}
    (fun A hA ↦ (mem_filter.1 hA).2) (by decide)
  revert A B
  decide

end Erdos702

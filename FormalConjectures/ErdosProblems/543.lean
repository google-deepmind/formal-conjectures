/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 543

*References:*
- [erdosproblems.com/543](https://www.erdosproblems.com/543)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErHa78b] Erdős, P. and Hall, R. R., _Some new results in probabilistic group theory_. Comment.
  Math. Helv. (1978), 448--457.
- [ErRe65] Erdős, P. and Rényi, A., _Probabilistic methods in group theory_. J. Analyse Math.
  (1965), 127-138.
-/

@[expose] public section

open Filter Finset Real

namespace Erdos543

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- `A` is *complete* if all elements of `G` can be written as $\sum_{x\in S}x$ for some
$S\subseteq A$. -/
def IsComplete (A : Finset G) : Prop := ∀ g : G, ∃ S ⊆ A, ∑ x ∈ S, x = g

open scoped Classical in
/-- The probability that a uniformly random `k`-element subset of `G` is complete. -/
noncomputable def completeProbability (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) : ℝ :=
  (((univ : Finset G).powersetCard k).filter IsComplete).card /
    ((univ : Finset G).powersetCard k).card

/-- `f N` is the minimal `k` such that, for every abelian group `G` of size `N`, a uniformly
random `k`-element subset of `G` is complete with probability at least `1/2`. -/
noncomputable def f (N : ℕ) : ℕ :=
  sInf {k | ∀ (G : Type) [AddCommGroup G] [Fintype G], Fintype.card G = N →
    1 / 2 ≤ completeProbability G k}

/--
Define $f(N)$ be the minimal $k$ such that the following holds: if $G$ is an abelian group of size
$N$ and $A\subseteq G$ is a random set of size $k$ then, with probability $\geq 1/2$, all elements
of $G$ can be written as $\sum_{x\in S}x$ for some $S\subseteq A$. Is
$$f(N) \leq \log_2 N+o(\log\log N)?$$

The answer is no: ChatGPT and Tang have disproved this, confirming Erdős' belief, showing that
if $f(N)\leq \log_2 N+o(\log\log N)$ then, for all large enough primes $p$, a random subset of
$\mathbb{F}_p$ of size $\leq f(p)$ fails to generate $\mathbb{F}_p$ in this way.

See also [1179](https://www.erdosproblems.com/1179).
-/
@[category research solved, AMS 5 11 20, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos543.lean#L81"]
theorem erdos_543 : answer(False) ↔
    ∃ o : ℕ → ℝ, (o =o[atTop] fun N : ℕ ↦ log (log N)) ∧
      ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ logb 2 N + o N := by
  sorry

/-- Erdős and Rényi [ErRe65] proved that $f(N) \leq \log_2N+O(\log\log N)$. -/
@[category research solved, AMS 5 11 20]
theorem erdos_543.variants.erdos_renyi :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ logb 2 N + C * log (log N) := by
  sorry

/-- Erdős and Hall [ErHa78b] proved that it is not true that
$f(N) \leq \log_2N+o(\log\log\log N)$. -/
@[category research solved, AMS 5 11 20]
theorem erdos_543.variants.erdos_hall :
    ¬ ∃ o : ℕ → ℝ, (o =o[atTop] fun N : ℕ ↦ log (log (log N))) ∧
      ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ logb 2 N + o N := by
  sorry

end Erdos543

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
# Erdős Problem 783

*References:*
- [erdosproblems.com/783](https://www.erdosproblems.com/783)
- [Er73] Erdős, P., Problems and results on combinatorial number theory. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [ErRu80] Erdős, P. and Ruzsa, I. Z., On the small sieve. I. Sifting by primes. J. Number Theory
  (1980), 385--394.
- [Hi87b] Hildebrand, Adolf, Quantitative mean value theorems for nonnegative multiplicative
  functions. II. Acta Arith. (1987), 209--260.
-/

@[expose] public section

open Filter Real Topology

namespace Erdos783

/-- The integers in `{1, …, N}` not divisible by any element of `A`. -/
def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m ↦ ∀ a ∈ A, ¬ a ∣ m

/-- A set `A ⊆ {2, …, N}` is *admissible* for the budget `C` if its elements are pairwise coprime
and `∑_{a ∈ A} 1/a ≤ C`. -/
def IsAdmissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 N ∧ (A : Set ℕ).Pairwise Nat.Coprime ∧ ∑ a ∈ A, (1 / a : ℝ) ≤ C

/-- The minimum number of integers in `{1, …, N}` not divisible by any element of an admissible
set `A ⊆ {2, …, N}` with reciprocal sum at most `C`. -/
noncomputable def minUnsieved (C : ℝ) (N : ℕ) : ℕ :=
  sInf {k | ∃ A, IsAdmissible C N A ∧ k = (unsieved N A).card}

/-- `ρ` is the Dickman–de Bruijn function: it is continuous on `[0, ∞)`, equal to `1` on `[0, 1]`,
and satisfies the delay differential equation `u ρ'(u) = -ρ(u - 1)` for `u > 1`. These conditions
determine `ρ` uniquely on `[0, ∞)`. -/
def IsDickman (ρ : ℝ → ℝ) : Prop :=
  ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u > 1, HasDerivAt ρ (-ρ (u - 1) / u) u

open scoped Classical in
/-- The block of the largest primes `q₁ > q₂ > ⋯ > q_k` up to `N` with `∑ 1/q_i ≤ C`, `k`
maximal: the primes `p ≤ N` with `∑_{p ≤ q ≤ N, q prime} 1/q ≤ C`. -/
noncomputable def primeBlock (C : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun p ↦
    p.Prime ∧ ∑ q ∈ (Finset.Icc p N).filter Nat.Prime, (1 / q : ℝ) ≤ C

/--
Fix some constant $C>0$ and let $N$ be large. Let $A\subseteq \{2,\ldots,N\}$ be such that
$(a,b)=1$ for all $a\neq b\in A$ and $\sum_{n\in A}\frac{1}{n}\leq C$.

What choice of such an $A$ minimises the number of integers $m\leq N$ not divisible by any
$a\in A$?

Tao has resolved this question asymptotically: the minimum number of integers in $[1,N]$ not
divisible by any $a\in A$ is $(\rho(e^C)+o(1))N$, where $\rho$ is the Dickman–de Bruijn function
and the $o(1)$ term $\to 0$ as $N\to\infty$ with fixed $C$. The upper bound is achieved by the
block of the largest primes up to $N$ with reciprocal sum at most $C$, see `primeBlock`.

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos783.lean#L47"]
theorem erdos_783 (ρ : ℝ → ℝ) (hρ : IsDickman ρ) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ ↦ (minUnsieved C N : ℝ) / N) atTop (𝓝 (ρ (exp C))) := by
  sorry

/--
Tao's lower bound, uniform in the admissible set: for every fixed $C>0$ and $\varepsilon>0$, for
all sufficiently large $N$ every admissible $A\subseteq\{2,\ldots,N\}$ leaves at least
$(\rho(e^C)-\varepsilon)N$ integers in $[1,N]$ not divisible by any $a\in A$.

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos783.lean#L39"]
theorem erdos_783.variants.tao_lower_bound (ρ : ℝ → ℝ) (hρ : IsDickman ρ) (C : ℝ) (hC : 0 < C)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, IsAdmissible C N A →
      (ρ (exp C) - ε) * N < (unsieved N A).card := by
  sorry

/--
Hildebrand [Hi87b] proved the corresponding lower bound when $A$ is a set of primes, answering a
question of Erdős and Ruzsa [ErRu80]: for every fixed $C>0$ and $\varepsilon>0$, for all
sufficiently large $N$ every admissible set of primes $P\subseteq\{2,\ldots,N\}$ leaves at least
$(\rho(e^{\sum_{p\in P}1/p})-\varepsilon)N$ integers in $[1,N]$ not divisible by any $p\in P$.

This was formalized in Lean by Codex and GPT-5.6 Sol.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos783/PrimeLower.lean#L422"]
theorem erdos_783.variants.hildebrand (ρ : ℝ → ℝ) (hρ : IsDickman ρ) (C : ℝ) (hC : 0 < C)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, IsAdmissible C N P →
      (∀ p ∈ P, p.Prime) →
        (ρ (exp (∑ p ∈ P, (1 / p : ℝ))) - ε) * N < (unsieved N P).card := by
  sorry

/--
Erdős [Er73] suggests that the block `primeBlock C N` of the largest primes up to $N$ with
reciprocal sum at most $C$ 'either gives the extremal sequence (or at least nearly gives the
minimum)'. Is it the extremal set for all $C>0$ and all sufficiently large $N$?

Chojecki has proved that this is the extremal set when $C\leq\log 2$. Hunter has noted that there
are cases where it is not the literal extremal set, since small improving perturbations are
possible.
-/
@[category research open, AMS 11]
theorem erdos_783.variants.prime_block :
    answer(sorry) ↔ ∀ C : ℝ, 0 < C → ∀ᶠ N : ℕ in atTop,
      (unsieved N (primeBlock C N)).card = minUnsieved C N := by
  sorry

end Erdos783

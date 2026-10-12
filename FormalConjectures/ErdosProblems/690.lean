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
# Erdős Problem 690

*References:*
- [erdosproblems.com/690](https://www.erdosproblems.com/690)
- [Er79e] Erdős, Paul, _Some unconventional problems in number theory_. Astérisque (1979), 73-82.
- [Ca25] S. Cambie, _Resolution of Erdős' problems about unimodularity_. arXiv:2501.10333 (2025).
-/

@[expose] public section

open Filter

namespace Erdos690

/-- The set of positive integers whose `k`-th smallest prime factor is `p`: if
$p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$. -/
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1}

/-- A function on the primes is *unimodular* if it first increases in $p$ until its maximum then
decreases. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m, m.Prime ∧ (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    ∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p

/--
Let $d_k(p)$ be the density of those integers whose $k$th smallest prime factor is $p$ (i.e. if
$p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$).

For fixed $k\geq 1$ is $d_k(p)$ unimodular in $p$? That is, it first increases in $p$ until its
maximum then decreases.

The answer is no in general: Cambie [Ca25] has shown that $d_k(p)$ is unimodular for
$1\leq k\leq 3$ and is not unimodular for $4\leq k\leq 20$.

The densities $d_k(p)$ exist (see `erdos_690.variants.hasDensity`), so the statement quantifies
over any function `d` recording them.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162"]
theorem erdos_690 : answer(False) ↔
    ∀ k ≥ 1, ∀ d : ℕ → ℝ,
      (∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) → IsUnimodalOnPrimes d := by
  sorry

/-- For every $k\geq 1$ and prime $p$, the set of integers whose $k$th smallest prime factor is
$p$ has a natural density. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162"]
theorem erdos_690.variants.hasDensity (k p : ℕ) (hk : 1 ≤ k) (hp : p.Prime) :
    ∃ δ : ℝ, (kthPrimeFactorSet k p).HasDensity δ := by
  sorry

/-- Cambie [Ca25] has shown that $d_k(p)$ is unimodular for $1\leq k\leq 3$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162"]
theorem erdos_690.variants.cambie_unimodal (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3)
    (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    IsUnimodalOnPrimes d := by
  sorry

/-- Cambie [Ca25] has shown that $d_k(p)$ is not unimodular for $4\leq k\leq 20$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162"]
theorem erdos_690.variants.cambie_not_unimodal (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20)
    (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    ¬ IsUnimodalOnPrimes d := by
  sorry

/-- Is $d_k(p)$ unimodular for any $k\geq 21$? -/
@[category research open, AMS 11]
theorem erdos_690.variants.large_k : answer(sorry) ↔
    ∃ k ≥ 21, ∀ d : ℕ → ℝ,
      (∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) → IsUnimodalOnPrimes d := by
  sorry

end Erdos690

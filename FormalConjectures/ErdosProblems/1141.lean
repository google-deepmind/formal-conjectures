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
# Erdős Problem 1141

*References:*
- [erdosproblems.com/1141](https://www.erdosproblems.com/1141)
- [A214583](https://oeis.org/A214583)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Or26] Y. Oriike, [Lean formalisation of Erdős problem 1141](https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean) (2026)
- [Po17] P. Pollack, Bounds for the first several prime character nonresidues. Proc. Amer. Math. Soc.
  (2017), 2815--2826.
- [Me1874] F. Mertens, Ein Beitrag zur analytischen Zahlentheorie. J. Reine Angew. Math. (1874),
  46--62.
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

open Nat Set

namespace Erdos1141

/- ## The two external inputs

The formal proof linked on `erdos_1141` below assumes both of these, and states neither. They are
recorded here so the `assuming` clause on that theorem can name them. -/

/-- The cutoff $m^{1/4 + \varepsilon}$ of Theorem 1.3 of [Po17]. -/
noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ := (m : ℝ) ^ ((1 / 4 : ℝ) + ε)

/--
The primes $\ell \leq m^{1/4+\varepsilon}$ with $\chi(\ell) = 1$.

This does not require $\chi$ to be quadratic. That hypothesis belongs to the theorem below, as it
does in the paper.
-/
noncomputable def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌈residuePrimeUpperBound m ε⌉₊ + 1)).filter fun ℓ =>
    ℓ.Prime ∧ (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (ℓ : ZMod m) = 1

/--
**Theorem 1.3 of [Po17]**: for a quadratic character to a large enough modulus, the primes below
$m^{1/4+\varepsilon}$ on which the character is $1$ outnumber any fixed power of $\log m$.
-/
@[category research solved, AMS 11]
theorem erdos_1141.variants.pollack_1_3 (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ < m → ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
      Real.log m ^ A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
  sorry

/--
**Mertens' third theorem** [Me1874], in the weakened form the linked proof assumes: the product
over the primes up to $n$ of $1 - 1/p$ is at least $1/(3\log n)$.

The true asymptotic is $e^{-\gamma}/\log n$, and $e^{-\gamma} > 1/3$, so this bound is weaker than
the theorem and is what the deduction needs.
-/
@[category research solved, AMS 11]
theorem erdos_1141.variants.mertens_third (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, le_sqrt, pow_two]

/--
Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$?

In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an
error, since for example $968-9=7\cdot 137$.

The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$
is $1722$.

The answer is negative: [APSSV26b] proves a stronger finiteness theorem, deducing it from
Pollack [Po17]. Oriike [Or26] formalised the deduction in Lean.

The linked proof is the deduction and not the whole result. It declares Theorem 1.3 of [Po17] and
Mertens' third theorem as axioms, so it is marked `conditional` and names both.
-/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean"
  assuming erdos_1141.variants.pollack_1_3 erdos_1141.variants.mertens_third]
theorem erdos_1141 :
    answer(False) ↔ Infinite { n | Erdos1141Prop n } := by
  sorry

@[category test, AMS 11]
example : ¬ Erdos1141Prop 968 := by
  decide +native

@[category test, AMS 11]
example : Erdos1141Prop 1722 := by
  decide +native

end Erdos1141

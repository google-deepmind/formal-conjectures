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
# Erdős Problem 292

*References:*
- [erdosproblems.com/292](https://www.erdosproblems.com/292)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ma00] Martin, Greg, *Denser Egyptian fractions*. Acta Arith. (2000), 231-260.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos292

/-- The set $A$ of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. -/
def A : Set ℕ :=
  {n | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1}

/--
Let $A$ be the set of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. Explore $A$. In particular, does $A$ have density $1$?

Straus observed that $A$ is closed under multiplication. Furthermore, it is easy to see that $A$
does not contain any prime power.

The answer is yes, as proved by Martin [Ma00], who in fact proved that if
$B=\mathbb{N}\backslash A$ then, for all large $x$,
$$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x},$$
and also gave an essentially complete description of $B$ as those integers which are small
multiples of prime powers.

van Doorn has observed that if $n\in A$ (with $n>1$) then $2n\in A$ also, since if
$\sum \frac{1}{m_i}=1$ then $\frac{1}{2}+\sum\frac{1}{2m_i}=1$ also.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos292.lean#L116"]
theorem erdos_292 : answer(True) ↔ A.HasDensity 1 := by
  sorry

/-- Martin [Ma00] proved that if $B=\mathbb{N}\backslash A$ then
$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x}$. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.martin :
    (fun x : ℕ ↦ ((Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) =Θ[atTop]
      fun x ↦ Real.log (Real.log x) / Real.log x := by
  sorry

/-- Straus observed that $A$ is closed under multiplication. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  sorry

/-- $A$ does not contain any prime power. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  sorry

/-- van Doorn observed that if $n\in A$ (with $n>1$) then $2n\in A$ also. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  sorry

end Erdos292

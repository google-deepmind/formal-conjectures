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
# Erdős Problem 980

*References:*
- [erdosproblems.com/980](https://www.erdosproblems.com/980)
- [El67b] Elliott, P. D. T. A., *A problem of Erdős concerning power residue sums*.
  Acta Arith. 13 (1967/68), 131-149.
- [Er61e] Erdős, P., *Remarks on number theory. I*. Mat. Lapok (1961), 10-17.
- [Er65b] Erdős, P., *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [MaPo11] Martin, G. and Pollack, P., *The average least character nonresidue and further
  variations on a theme of Erdős*. [arXiv:1112.1175](https://arxiv.org/abs/1112.1175) (2011).
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos980

/-- $n_k(p)$: the least positive integer which is not a $k$-th power residue modulo $p$. If every
integer is a $k$-th power residue (for example if $\gcd(k, p - 1) = 1$) the value is $0$; this
does not happen for the primes $p \equiv 1 \pmod k$ with $k \geq 2$ used below. -/
noncomputable def leastNonresidue (k p : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬ ∃ x : ZMod p, x ^ k = (n : ZMod p)}

/-- $\sum n_k(p)$ over the primes $p < x$ with $p \equiv 1 \pmod k$. -/
noncomputable def residueSum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1), (leastNonresidue k p : ℝ)

/-- $2$ is the least quadratic nonresidue modulo $3$. -/
@[category test, AMS 11]
theorem leastNonresidue_two_three : leastNonresidue 2 3 = 2 := by
  have h2 : 2 ∈ {n : ℕ | 0 < n ∧ ¬ ∃ x : ZMod 3, x ^ 2 = (n : ZMod 3)} :=
    ⟨by norm_num, by decide⟩
  refine le_antisymm (Nat.sInf_le h2) (le_csInf ⟨2, h2⟩ ?_)
  rintro n ⟨hn, hn'⟩
  by_contra! h
  have h1 : n = 1 := by omega
  subst h1
  exact hn' ⟨1, by decide⟩

/--
Let $k\geq 2$ and $n_k(p)$ denote the least $k$th power nonresidue of $p$. Is it true that
$$\sum_{p<x} n_k(p)\sim c_k \frac{x}{\log x}$$
for some constant $c_k>0$?

Erdős [Er65b] asked this; it is true, and was proved by Elliott [El67b]. As in [El67b], the sum
is over the primes $p \equiv 1 \pmod k$ (for each of which a $k$th power nonresidue exists).
-/
@[category research solved, question, AMS 11]
theorem erdos_980 (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x := by
  sorry

/--
Erdős [Er61e] proved this when $k=2$, with
$$c_2=\sum_{k=1}^\infty \frac{p_k}{2^k},$$
where $p_k$ is the $k$th prime; the sum is over the odd primes $p < x$ [MaPo11, (1.1)].
-/
@[category research solved, AMS 11]
theorem erdos_980.variants.erdos_two :
    residueSum 2 ~[atTop]
      fun x ↦ (∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1)) * x / Real.log x := by
  sorry

end Erdos980

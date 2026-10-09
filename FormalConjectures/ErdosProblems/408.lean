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
# Erdős Problem 408

*References:*
- [erdosproblems.com/408](https://www.erdosproblems.com/408)
- [OEIS A003434](https://oeis.org/A003434): the values $f(n)$ for $n \geq 2$.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980).
- [Pi29] Pillai, S. Sivasankaranarayana, *On a function connected with $\phi(n)$*. Bull. Amer.
  Math. Soc. 35 (1929), 837-841.
  [doi:10.1090/S0002-9904-1929-04800-6](https://doi.org/10.1090/S0002-9904-1929-04800-6)
- [Sh50] Shapiro, Harold N., *On the iterates of a certain class of arithmetic functions*. Comm.
  Pure Appl. Math. 3 (1950), 259-272.
- [EGPS90] Erdős, P., Granville, A., Pomerance, C. and Spiro, C., *On the normal behavior of the
  iterates of some arithmetic functions*. Analytic number theory (Allerton Park, IL, 1989),
  Progr. Math. 85 (1990), 165-204.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. Third edition, Springer (2004),
  Problem B41.
- [FKL10] Ford, K., Konyagin, S. V. and Luca, F., *Prime chains and Pratt trees*. Geom. Funct.
  Anal. 20 (2010), 1231-1258. [arXiv:0904.0473](https://arxiv.org/abs/0904.0473)
  [doi:10.1007/s00039-010-0089-0](https://doi.org/10.1007/s00039-010-0089-0)
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos408

/--
`f n` is $f(n) = \min\{k \geq 1 : \phi_k(n) = 1\}$, where $\phi_1 = \phi$ is Euler's totient
function and $\phi_k(n) = \phi(\phi_{k-1}(n))$. As in the source, $k$ starts at $1$, so
$f(1) = 1$. Every iterate of $\phi$ at $0$ is $0$, so `sInf ∅ = 0` gives the junk value
$f(0) = 0$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}

/-- The junk value $f(0) = 0$. -/
@[category test, AMS 11]
theorem f_zero : f 0 = 0 := by
  rw [f, Nat.sInf_eq_zero]
  refine Or.inr (Set.eq_empty_iff_forall_notMem.2 fun k hk ↦ ?_)
  have h := hk.2
  rw [Function.iterate_fixed Nat.totient_zero] at h
  omega

/-- $\phi(1) = 1$, so $f(1) = 1$ (the iteration count starts at $1$, not $0$). -/
@[category test, AMS 11]
theorem f_one : f 1 = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨le_rfl, by simp⟩
  · exact le_csInf ⟨1, le_rfl, by simp⟩ fun _ hk ↦ hk.1

/-- $\phi(2) = 1$, so $f(2) = 1$. -/
@[category test, AMS 11]
theorem f_two : f 2 = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨le_rfl, by simp⟩
  · exact le_csInf ⟨1, le_rfl, by simp⟩ fun _ hk ↦ hk.1

/-- Since $\phi(2^{j+1}) = 2^j$, we have $f(2^k) = k$ for every $k \geq 1$. -/
@[category test, AMS 11]
theorem f_two_pow (k : ℕ) (hk : 1 ≤ k) : f (2 ^ k) = k := by
  have key : ∀ j, j ≤ k → Nat.totient^[j] (2 ^ k) = 2 ^ (k - j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega)]
      obtain ⟨i, hi⟩ : ∃ i, k - j = i + 1 := ⟨k - j - 1, by omega⟩
      rw [hi, Nat.totient_prime_pow_succ Nat.prime_two, show k - (j + 1) = i by omega]
      simp
  have hk1 : Nat.totient^[k] (2 ^ k) = 1 := by rw [key k le_rfl, Nat.sub_self, pow_zero]
  apply le_antisymm
  · exact Nat.sInf_le ⟨hk, hk1⟩
  refine le_csInf ⟨k, hk, hk1⟩ fun j hj ↦ ?_
  by_contra hlt
  have h2 : 2 ≤ 2 ^ (k - j) := Nat.le_self_pow (by omega) 2
  have h3 := hj.2
  rw [key j (by omega)] at h3
  omega

/--
Let $\phi(n)$ be the Euler totient function and $\phi_k(n)$ be the iterated $\phi$ function, so
that $\phi_1(n)=\phi(n)$ and $\phi_k(n)=\phi(\phi_{k-1}(n))$. Let
$$f(n) = \min\{k : \phi_k(n)=1\}.$$
Does $f(n)/\log n$ have a distribution function?

We ask for a distribution function $F$ (non-decreasing, with $F(-\infty) = 0$ and
$F(+\infty) = 1$) such that, for every continuity point $c$ of $F$, the set
$\{n : f(n)/\log n \leq c\}$ has natural density $F(c)$. For $n \leq 1$ the quotient is $0$ in
Lean, which does not affect densities. Erdős, Granville, Pomerance and Spiro [EGPS90] proved
that the answer is yes, conditional on a form of the Elliott–Halberstam conjecture.
-/
@[category research open, AMS 11]
theorem erdos_408.parts.i : answer(sorry) ↔
    ∃ F : ℝ → ℝ, Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) ∧
      ∀ c : ℝ, ContinuousAt F c →
        {n : ℕ | (f n : ℝ) / Real.log n ≤ c}.HasDensity (F c) := by
  sorry

/--
Is $f(n)/\log n$ almost always constant?

We read this as: is there a constant $\alpha$ such that, for every $\epsilon > 0$, the set of
$n$ with $|f(n)/\log n - \alpha| < \epsilon$ has natural density $1$? Erdős, Granville,
Pomerance and Spiro [EGPS90] proved that, conditional on a form of the Elliott–Halberstam
conjecture, $f(n)$ has normal order $\alpha \log n$ for some constant $\alpha > 0$, so that the
answer is yes under this hypothesis.
-/
@[category research open, AMS 11]
theorem erdos_408.parts.ii : answer(sorry) ↔
    ∃ α : ℝ, ∀ ε > (0 : ℝ),
      {n : ℕ | |(f n : ℝ) / Real.log n - α| < ε}.HasDensity 1 := by
  sorry

/--
Pillai [Pi29] proved that, for all $n \geq 2$,
$$\left\lfloor \frac{\log n - \log 2}{\log 3} \right\rfloor + 1 \leq f(n) \leq
  \left\lfloor \frac{\log n}{\log 2} \right\rfloor + 1.$$
These are Theorems I and III of [Pi29]; Pillai's function $R(n)$ is the least $r$ with
$\phi_r(n) = 1$, which is $f(n)$. The lower bound is attained at $n = 2 \cdot 3^k$, and
$f(2^k) = k$ (`Erdos408.f_two_pow`), so the upper bound cannot be replaced by $f(n) < \log_2 n$.
-/
@[category research solved, AMS 11]
theorem erdos_408.variants.pillai (n : ℕ) (hn : 2 ≤ n) :
    ⌊(Real.log n - Real.log 2) / Real.log 3⌋₊ + 1 ≤ f n ∧
      f n ≤ ⌊Real.log n / Real.log 2⌋₊ + 1 := by
  sorry

/--
The third question asks what can be said about the largest prime factor $P^+(\phi_k(n))$ when,
say, $k = \log\log n$; it is open-ended and is not formalised. The site remarks that it is likely
true that, if $k \to \infty$ however slowly with $n$, then $P^+(\phi_k(n)) \leq n^{o(1)}$ for
almost all $n$.

Ford, Konyagin and Luca [FKL10, Theorem 5] proved that for every $\epsilon > 0$ and $\delta > 0$
there is an integer $k$ such that, for all large $x$, at least $(1 - \epsilon)x$ integers
$n \leq x$ satisfy $P^+(\phi_k(n)) \leq x^{\delta}$. Since $P^+(\phi(m)) \leq P^+(m)$, this gives
the remark above for every $k = k(n) \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_408.variants.ford_konyagin_luca (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card := by
  sorry

end Erdos408

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
# Erdős Problem 420

*References:*
- [erdosproblems.com/420](https://www.erdosproblems.com/420)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [EGIP96] Erdős, P. and Graham, S. W. and Ivić, A. and Pomerance, C., *On the number of divisors
  of $n!$*. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995), Progr. Math. 138, Birkhäuser
  Boston (1996), 337-355.
-/

@[expose] public section

open Filter
open scoped ArithmeticFunction.sigma

namespace Erdos420

/--
`F f n` is
$$F(f,n)=\frac{\tau((n+\lfloor f(n)\rfloor)!)}{\tau(n!)},$$
where $\tau = \sigma_0$ counts divisors. We use the natural floor `⌊f n⌋₊`, which agrees with
$\lfloor f(n) \rfloor$ when $f(n) \geq 0$ and is $0$ when $f(n) < 0$.
-/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (σ 0 (n + ⌊f n⌋₊).factorial : ℝ) / (σ 0 n.factorial : ℝ)

/-- If $f(n) < 1$ then the natural floor `⌊f n⌋₊` is $0$, so $F(f, n) = 1$. -/
@[category test, AMS 11]
theorem F_eq_one_of_lt_one {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) : F f n = 1 := by
  have h : (σ 0 n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)).ne'
  rw [F, Nat.floor_eq_zero.2 hf, add_zero, div_self h]

/-- $n!$ divides $(n + k)!$, so $F(f, n) \geq 1$ always. -/
@[category test, AMS 11]
theorem one_le_F (f : ℕ → ℝ) (n : ℕ) : 1 ≤ F f n := by
  have h0 : (0 : ℝ) < σ 0 n.factorial := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  rw [F, one_le_div h0]
  simp only [ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
    (Nat.factorial_dvd_factorial (Nat.le_add_right n _)))

/-- If $p = n + 1$ is prime then $p$ does not divide $n!$, so $\tau((n+1)!) = 2\tau(n!)$ and
$F(1, n) = 2$. -/
@[category test, AMS 11]
theorem F_one_of_prime {n : ℕ} (hn : (n + 1).Prime) : F (fun _ ↦ 1) n = 2 := by
  have hcop : Nat.Coprime (n + 1) n.factorial :=
    (Nat.Prime.coprime_iff_not_dvd hn).2 fun h ↦ by
      have := (Nat.Prime.dvd_factorial hn).1 h
      omega
  have h0 : (σ 0 n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)).ne'
  have hp : σ 0 (n + 1) = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hn
  simp only [F, Nat.floor_one, Nat.factorial_succ,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hp]
  push_cast
  field_simp

/--
If $\tau(n)$ counts the number of divisors of $n$ then let
$$F(f,n)=\frac{\tau((n+\lfloor f(n)\rfloor)!)}{\tau(n!)}.$$
Is it true that
$$\lim_{n\to \infty}F((\log n)^C,n)=\infty$$
for large $C$?

"For large $C$" means for all sufficiently large real $C$. Since $(\log n)^C$ increases with $C$
for $n \geq 3$ and $F(f,n)$ is nondecreasing in $f(n)$, this is equivalent to asking for one
such $C$.
-/
@[category research open, AMS 11]
theorem erdos_420.parts.i : answer(sorry) ↔
    ∀ᶠ C : ℝ in atTop, Tendsto (F fun m ↦ Real.log m ^ C) atTop atTop := by
  sorry

/--
Is it true that $F(\log n,n)$ is everywhere dense in $(1,\infty)$?

This asks that every point of $(1,\infty)$ lies in the closure of the set of values
$F(\log n, n)$. Note that $F(f,n) \geq 1$ always (`Erdos420.one_le_F`).
-/
@[category research open, AMS 11]
theorem erdos_420.parts.ii : answer(sorry) ↔
    Set.Ioi (1 : ℝ) ⊆ closure (Set.range (F fun m ↦ Real.log m)) := by
  sorry

/--
More generally, if $f(n)\leq \log n$ is a monotonic function such that $f(n)\to \infty$ as
$n\to \infty$, then is $F(f,n)$ everywhere dense?

"Everywhere dense" means dense in $(1,\infty)$, as in `Erdos420.erdos_420.parts.ii`. Asking for
$f(n) \leq \log n$ for all $n$, rather than for all large $n$, gives an equivalent question.
-/
@[category research open, AMS 11]
theorem erdos_420.parts.iii : answer(sorry) ↔
    ∀ f : ℕ → ℝ, Monotone f → (∀ n, f n ≤ Real.log n) → Tendsto f atTop atTop →
      Set.Ioi (1 : ℝ) ⊆ closure (Set.range (F f)) := by
  sorry

/--
Erdős, Graham, Ivić and Pomerance proved [EGIP96, Corollary 2] that $K(n)/\log n$ is unbounded,
where $K(n)$ is the least $K \geq 1$ with $\tau((n+K)!) \geq 2\tau(n!)$. Equivalently, for every
$c > 0$ we have $F(c\log n, n) < 2$ for infinitely many $n$. In particular
$\liminf F(c\log n, n) \leq 2$.
-/
@[category research solved, AMS 11]
theorem erdos_420.variants.log_frequently_lt_two :
    ∀ c > (0 : ℝ), ∃ᶠ n : ℕ in atTop, F (fun m ↦ c * Real.log m) n < 2 := by
  sorry

/--
Erdős, Graham, Ivić and Pomerance proved [EGIP96, Corollary 2] that for infinitely many $n$,
$$K(n) > \frac{\log n \cdot \log\log n \cdot \log\log\log\log n}{9(\log\log\log n)^3},$$
where $K(n)$ is the least $K \geq 1$ with $\tau((n+K)!) \geq 2\tau(n!)$. Equivalently,
$F(f,n) < 2$ for infinitely many $n$, where $f(n)$ is the right-hand side.
-/
@[category research solved, AMS 11]
theorem erdos_420.variants.rankin_frequently_lt_two :
    ∃ᶠ n : ℕ in atTop, F (fun m ↦ Real.log m * Real.log (Real.log m) *
      Real.log (Real.log (Real.log (Real.log m))) /
        (9 * Real.log (Real.log (Real.log m)) ^ 3)) n < 2 := by
  sorry

/--
Erdős, Graham, Ivić and Pomerance proved [EGIP96, Corollary 3] that for all sufficiently large
$n$ we have $K(n) < n^{4/9}$, where $K(n)$ is the least $K \geq 1$ with
$\tau((n+K)!) \geq 2\tau(n!)$. Hence $F(n^{4/9}, n) \geq 2$ for all large $n$.
-/
@[category research solved, AMS 11]
theorem erdos_420.variants.pow_four_ninths :
    ∀ᶠ n : ℕ in atTop, 2 ≤ F (fun m ↦ (m : ℝ) ^ (4 / 9 : ℝ)) n := by
  sorry

end Erdos420

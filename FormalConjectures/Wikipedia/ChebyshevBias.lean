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
# Chebyshev's bias

Let $\pi(n; q, r)$ count primes $p \le n$ satisfying $p \equiv r \pmod q$. Pafnuty Chebyshev
(1853) noted that $\pi(n; 4, 3)$ usually exceeds $\pi(n; 4, 1)$. John E. Littlewood (1914)
established that $\pi(n; 4, 3) - \pi(n; 4, 1)$ switches sign infinitely often (first becoming
negative at $n = 26861$), and Stanisław Knapowski and Pál Turán's (1962) conjecture that
$\{n \in \mathbb{N} : \pi(n; 4, 3) > \pi(n; 4, 1)\}$ has natural density $1$ was disproved.
Assuming GRH and linear independence of positive ordinates of
Dirichlet $L$-zeros, Michael Rubinstein and Peter Sarnak (1994) showed this set has logarithmic
density $\delta_{4; 3, 1} \approx 0.9959 \in (1/2, 1)$, and more generally that coprime
quadratic nonresidues modulo $q \ge 3$ lead coprime quadratic residues with logarithmic density
in $(1/2, 1)$; proving this unconditionally remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Chebyshev%27s_bias)
- J. E. Littlewood, *Sur la distribution des nombres premiers*, C. R. Acad. Sci. **158**
  (1914), 1869–1872.
- M. Rubinstein and P. Sarnak, *Chebyshev's bias*, Experiment. Math. **3** (1994), 173–197.
-/

@[expose] public section

namespace ChebyshevBias

/-- Count $\pi(n; q, r)$ of primes $p \le n$ satisfying $p \equiv r \pmod q$. -/
def primeCountMod (q r n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun p => p.Prime ∧ p % q = r % q).card

/-- Count $\pi(n; 4, r)$ of primes $p \le n$ congruent to $r$ modulo $4$. -/
abbrev primeCountModFour (r n : ℕ) : ℕ :=
  primeCountMod 4 r n

/-- Integers $n \in \mathbb{N}$ where $\pi(n; 4, 3) > \pi(n; 4, 1)$. -/
def chebyshevModFourLeadSet : Set ℕ :=
  {n : ℕ | primeCountModFour 1 n < primeCountModFour 3 n}

/-- At $n = 10$, $\pi(10; 4, 3) = 2$ exceeds $\pi(10; 4, 1) = 1$, so `10` belongs to
`chebyshevModFourLeadSet`. -/
@[category test, AMS 11]
theorem ten_mem_chebyshevModFourLeadSet : 10 ∈ chebyshevModFourLeadSet := by
  change primeCountModFour 1 10 < primeCountModFour 3 10
  decide

/-- At $n = 5$, $\pi(5; 4, 3) = 1$ equals $\pi(5; 4, 1) = 1$, so `5` does not belong to
`chebyshevModFourLeadSet`. -/
@[category test, AMS 11]
theorem five_notMem_chebyshevModFourLeadSet : 5 ∉ chebyshevModFourLeadSet := by
  change ¬ (primeCountModFour 1 5 < primeCountModFour 3 5)
  decide

/-- Littlewood's oscillation theorem (1914): both $\pi(n; 4, 3) > \pi(n; 4, 1)$ and
$\pi(n; 4, 1) > \pi(n; 4, 3)$ hold for infinitely many $n \in \mathbb{N}$. -/
@[category research solved, AMS 11]
theorem littlewood_mod_four_sign_changes :
    chebyshevModFourLeadSet.Infinite ∧
      {n : ℕ | primeCountModFour 3 n < primeCountModFour 1 n}.Infinite := by
  sorry

/-- Refutation of the Knapowski–Turán natural-density conjecture: the set of $n \in \mathbb{N}$
with $\pi(n; 4, 3) > \pi(n; 4, 1)$ does not have natural density $1$. -/
@[category research solved, AMS 11]
theorem knapowski_turan_natural_density_false :
    ¬ chebyshevModFourLeadSet.HasDensity 1 := by
  sorry

/-- Unconditional Rubinstein–Sarnak Chebyshev bias conjecture modulo $4$: the set of
$n \in \mathbb{N}$ satisfying $\pi(n; 4, 3) > \pi(n; 4, 1)$ admits a logarithmic density
$\delta \in (1/2, 1)$. -/
@[category research open, AMS 11]
theorem rubinstein_sarnak_unconditional_chebyshev_bias :
    ∃ δ : ℝ, (1 : ℝ) / 2 < δ ∧ δ < 1 ∧ Set.HasLogDensity chebyshevModFourLeadSet δ := by
  sorry

/-- General-modulus Chebyshev bias conjecture: for any modulus $q \ge 3$ and integers $a, b$
coprime to $q$ such that $a$ is a quadratic residue modulo $q$ and $b$ is a quadratic nonresidue
modulo $q$, the set $\{n \in \mathbb{N} : \pi(n; q, b) > \pi(n; q, a)\}$ admits a logarithmic
density $\delta \in (1/2, 1)$. -/
@[category research open, AMS 11]
theorem rubinstein_sarnak_unconditional_chebyshev_bias.variants.general_modulus
    (q a b : ℕ) (hq : 3 ≤ q) (ha : a.Coprime q) (hb : b.Coprime q)
    (hres : IsSquare (a : ZMod q)) (hnonres : ¬ IsSquare (b : ZMod q)) :
    ∃ δ : ℝ, (1 : ℝ) / 2 < δ ∧ δ < 1 ∧
      Set.HasLogDensity {n : ℕ | primeCountMod q a n < primeCountMod q b n} δ := by
  sorry

end ChebyshevBias

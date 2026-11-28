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

Let $\pi(n; q, r)$ (`Nat.primeCountingMod n q r`) count primes $p \le n$ satisfying
$p \equiv r \pmod q$. Pafnuty Chebyshev (1853) noted that $\pi(n; 4, 3)$ usually exceeds
$\pi(n; 4, 1)$. John E. Littlewood (1914) established that $\pi(n; 4, 3) - \pi(n; 4, 1)$ switches
sign infinitely often (first becoming negative at $n = 26861$). Jerzy Kaczorowski (1995) disproved
Stanisław Knapowski and Pál Turán's (1962) conjecture that
$\{n \in \mathbb{N} : \pi(n; 4, 3) > \pi(n; 4, 1)\}$ has natural density $1$ assuming GRH for
$L(s, \chi_4)$, whereas Kevin Ford, Sergei Konyagin, and Youness Lamzouri (2013) showed that
hypothetical off-critical zeros could force natural density $0$ or $1$. Assuming GRH and linear
independence of positive ordinates of Dirichlet $L$-zeros, Michael Rubinstein and Peter Sarnak
(1994) showed this set has logarithmic density $\delta_{4; 3, 1} \approx 0.9959 \in (1/2, 1)$, and
more generally that coprime quadratic nonresidues modulo $q \ge 3$ lead coprime quadratic residues
with logarithmic density in $(1/2, 1)$; proving this unconditionally remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Chebyshev%27s_bias)
- J. E. Littlewood, *Sur la distribution des nombres premiers*, C. R. Acad. Sci. **158**
  (1914), 1869–1872.
- M. Rubinstein and P. Sarnak, *Chebyshev's bias*, Experiment. Math. **3** (1994), 173–197.
- J. Kaczorowski, *On the distribution of primes ($\bmod\, 4$)*, Analysis **15** (1995), no. 2,
  159–171.
- K. Ford, S. Konyagin, and Y. Lamzouri, *The prime number race and zeros of Dirichlet
  $L$-functions off the critical line. III*, Quart. J. Math. **64** (2013), no. 4, 1091–1098
  (`arXiv:1204.6715`).
-/

@[expose] public section

namespace ChebyshevBias

/-- Integers $n \in \mathbb{N}$ where $\pi(n; 4, 3) > \pi(n; 4, 1)$. -/
def chebyshevModFourLeadSet : Set ℕ :=
  {n : ℕ | n.primeCountingMod 4 1 < n.primeCountingMod 4 3}

/-- At $n = 10$, $\pi(10; 4, 3) = 2$ exceeds $\pi(10; 4, 1) = 1$, so `10` belongs to
`chebyshevModFourLeadSet`. -/
@[category test, AMS 11]
theorem ten_mem_chebyshevModFourLeadSet : 10 ∈ chebyshevModFourLeadSet := by
  change Nat.primeCountingMod 10 4 1 < Nat.primeCountingMod 10 4 3
  decide

/-- At $n = 5$, $\pi(5; 4, 3) = 1$ equals $\pi(5; 4, 1) = 1$, so `5` does not belong to
`chebyshevModFourLeadSet`. -/
@[category test, AMS 11]
theorem five_notMem_chebyshevModFourLeadSet : 5 ∉ chebyshevModFourLeadSet := by
  change ¬ (Nat.primeCountingMod 5 4 1 < Nat.primeCountingMod 5 4 3)
  decide

/-- Littlewood's oscillation theorem (1914): both $\pi(n; 4, 3) > \pi(n; 4, 1)$ and
$\pi(n; 4, 1) > \pi(n; 4, 3)$ hold for infinitely many $n \in \mathbb{N}$. -/
@[category research solved, AMS 11]
theorem littlewood_mod_four_sign_changes :
    chebyshevModFourLeadSet.Infinite ∧
      {n : ℕ | n.primeCountingMod 4 3 < n.primeCountingMod 4 1}.Infinite := by
  sorry

/-- Conditional refutation of the Knapowski–Turán natural-density conjecture (Kaczorowski 1995):
assuming the Generalized Riemann Hypothesis for $L(s, \chi_4)$, the set of $n \in \mathbb{N}$ with
$\pi(n; 4, 3) > \pi(n; 4, 1)$ does not have natural density $1$. (Ford, Konyagin, and Lamzouri,
`arXiv:1204.6715`, showed that hypothetical off-critical zeros could make the natural density $0$
or $1$.) -/
@[category research solved, AMS 11]
theorem knapowski_turan_natural_density_false
    (hGRH : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) :
    ¬ chebyshevModFourLeadSet.HasDensity 1 := by
  sorry

/-- Unconditional Rubinstein–Sarnak Chebyshev bias conjecture modulo $4$ (obtained by removing GRH
and the linear independence hypothesis LI from Rubinstein and Sarnak's conditional theorem): the
set of $n \in \mathbb{N}$ satisfying $\pi(n; 4, 3) > \pi(n; 4, 1)$ admits a logarithmic density
$\delta \in (1/2, 1)$. -/
@[category research open, AMS 11]
theorem rubinstein_sarnak_unconditional_chebyshev_bias :
    ∃ δ : ℝ, (1 : ℝ) / 2 < δ ∧ δ < 1 ∧ Set.HasLogDensity chebyshevModFourLeadSet δ := by
  sorry

/-- Unconditional general-modulus Chebyshev bias conjecture (obtained by removing GRH and the
linear independence hypothesis LI from Rubinstein and Sarnak's conditional theorem): for any
modulus $q \ge 3$ and integers $a, b$ coprime to $q$ such that $a$ is a quadratic residue modulo
$q$ and $b$ is a quadratic nonresidue modulo $q$, the set
$\{n \in \mathbb{N} : \pi(n; q, b) > \pi(n; q, a)\}$ admits a logarithmic density
$\delta \in (1/2, 1)$. -/
@[category research open, AMS 11]
theorem rubinstein_sarnak_unconditional_chebyshev_bias.variants.general_modulus
    (q a b : ℕ) (hq : 3 ≤ q) (ha : a.Coprime q) (hb : b.Coprime q)
    (hres : IsSquare (a : ZMod q)) (hnonres : ¬ IsSquare (b : ZMod q)) :
    ∃ δ : ℝ, (1 : ℝ) / 2 < δ ∧ δ < 1 ∧
      Set.HasLogDensity {n : ℕ | n.primeCountingMod q a < n.primeCountingMod q b} δ := by
  sorry

end ChebyshevBias

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
# Erdős Problem 687

*References:*
- [erdosproblems.com/687](https://www.erdosproblems.com/687)
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence,
  *Long gaps between primes*. J. Amer. Math. Soc. (2018), 65-105.
- [Iw78] Iwaniec, Henryk, *On the problem of {J}acobsthal*. Demonstratio Math. (1978), 225--231.
- [MaPo90] Maier, Helmut and Pomerance, Carl, *Unusually large gaps between consecutive primes*.
  Trans. Amer. Math. Soc. (1990), 201--237.
- [OAI26a] OpenAI, *A quadratic bound for Jacobsthal's function*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf
- [Ra38] Rankin, R. A., *The difference between consecutive prime numbers*. J. London Math. Soc.
  (1938), 242--247.

This is the same problem as Ben Green's Open Problem 46 (`Green46.maxY`), and $Y(x) + 1$ is
Jacobsthal's function of the primorial $\prod_{p \le x} p$ (see Erdős Problem 970 and
[FGKMT18, (1.3)]).
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace Erdos687

/-- Can the interval $[1, y]$ be covered by congruence classes $a_p \pmod p$, one for each
prime $p \le x$? -/
def IsCoveredByResidues (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]

/-- $Y(x)$, the maximal $y$ such that $[1, y]$ can be covered, cast to a real number for
asymptotics. -/
noncomputable def Y (x : ℕ) : ℝ :=
  ((sSup { y | IsCoveredByResidues x y } : ℕ) : ℝ)

/--
Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence classes $a_p$ for
all primes $p \le x$ such that every integer in $[1, y]$ is congruent to at least one of the
$a_p \pmod p$. Give good estimates for $Y(x)$.
-/
@[category research open, AMS 11]
theorem erdos_687 :
    Y =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
In particular, can one prove that $Y(x) = o(x^2)$?

Yes. OpenAI [OAI26a] proved $h(k) \ll k^2 / (\log\log 3k)^2$ for Jacobsthal's function $h$
(Erdős Problem 970). By the Chinese remainder theorem $Y(x) < h(\pi(x))$, so
$Y(x) \ll (x+1)^2 / (\log\log 3(x+1))^2$; see `erdos_687.variants.upper_iterated_log`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/30k30/scholia/blob/af06f47d8ccf2247a3d1ebbb97fa261d103e7f83/erdos-687/glue/JacobsthalTo687.lean#L333"]
theorem erdos_687.parts.i : answer(True) ↔
    Y =o[atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2) := by
  sorry

/--
Or even $Y(x) \ll x^{1+o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_687.parts.ii : answer(sorry) ↔
    ∃ o : ℕ → ℝ, (o =o[atTop] fun _ : ℕ ↦ (1 : ℝ)) ∧
      Y ≪ fun x ↦ (x : ℝ) ^ (1 + o x) := by
  sorry

/-- Iwaniec [Iw78] proved $Y(x) \ll x^2$. -/
@[category research solved, AMS 11]
theorem erdos_687.variants.upper_iwaniec :
    Y ≪ fun x : ℕ ↦ (x : ℝ) ^ 2 := by
  sorry

/-- The bound $Y(x) \ll (x+1)^2 / (\log\log 3(x+1))^2$, from the Jacobsthal bound of
[OAI26a] via the Chinese remainder theorem. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/30k30/scholia/blob/af06f47d8ccf2247a3d1ebbb97fa261d103e7f83/erdos-687/glue/JacobsthalTo687.lean#L338"]
theorem erdos_687.variants.upper_iterated_log :
    Y ≪ fun x : ℕ ↦ ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2 := by
  sorry

/-- Ford, Green, Konyagin, Maynard and Tao [FGKMT18] proved
$Y(x) \gg x \frac{\log x \log\log\log x}{\log\log x}$, improving on Rankin [Ra38]. -/
@[category research solved, AMS 11]
theorem erdos_687.variants.lower :
    (fun x : ℕ ↦ (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
      Real.log (Real.log x)) ≪ Y := by
  sorry

/-- Maier and Pomerance conjectured that $Y(x) \ll x (\log x)^{2+o(1)}$. -/
@[category research open, AMS 11]
theorem erdos_687.variants.maier_pomerance :
    ∃ o : ℕ → ℝ, (o =o[atTop] fun _ : ℕ ↦ (1 : ℝ)) ∧
      Y ≪ fun x ↦ (x : ℝ) * Real.log x ^ (2 + o x) := by
  sorry

-- TODO: Erdős [Er80] also asked about the variant in which all but $o(y / \log y)$ of the
-- integers in $[1, y]$ are covered, and whether the answer is very different.

end Erdos687

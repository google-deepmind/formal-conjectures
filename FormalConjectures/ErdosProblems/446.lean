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
# Erdős Problem 446

*References:*
- [erdosproblems.com/446](https://www.erdosproblems.com/446)
- [OEIS A399690](https://oeis.org/A399690) and [OEIS A399691](https://oeis.org/A399691): the
  numerators and denominators of the rational numbers $\delta(n)$.
- [OEIS A399697](https://oeis.org/A399697) and [OEIS A399698](https://oeis.org/A399698): the
  numerators and denominators of the rational numbers $\delta_1(n)$.
- [OEIS A074738](https://oeis.org/A074738): the constant $\alpha$.
- [Be34] Besicovitch, A., *On the density of certain sequences of integers*. Math. Annalen (1934),
  336--341.
- [Er35] Erdős, Paul, *Note on Sequences of Integers No One of Which is Divisible By Any Other*.
  J. London Math. Soc. (1935), 126--128.
- [Er60] Erdős, P., *An asymptotic inequality in the theory of numbers*. Vestnik Leningrad. Univ.
  (1960), 41--49.
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval*. Ann. of
  Math. (2) (2008), 367--433.
- [Te84] Tenenbaum, G., *Sur la probabilité qu'un entier possède un diviseur dans un intervalle
  donné*. Compositio Math. (1984), 243--263.
-/

@[expose] public section

open Filter

open scoped Asymptotics

namespace Erdos446

/-- The least common multiple of the integers in the open interval $(n, 2n)$. Having a divisor in
$(n, 2n)$ is a periodic property of an integer, with period `intervalLcm n`. -/
def intervalLcm (n : ℕ) : ℕ :=
  (Finset.Ioo n (2 * n)).lcm id

/-- The number of divisors of $m$ lying in the open interval $(n, 2n)$. -/
def divisorCount (n m : ℕ) : ℕ :=
  ((Finset.Ioo n (2 * n)).filter fun d ↦ d ∣ m).card

/-- $\delta(n)$, the density of the integers which are divisible by some integer in $(n, 2n)$.
Since this set is periodic with period `intervalLcm n`, its natural density is the proportion of
residues modulo `intervalLcm n` which lie in it. The values are recorded in OEIS A399690 and
A399691. -/
noncomputable def delta (n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ 0 < divisorCount n m)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

/-- The Erdős–Tenenbaum–Ford constant $\alpha = 1 - \frac{1 + \log\log 2}{\log 2}$. -/
noncomputable def alpha446 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- The denominator $(\log n)^\alpha (\log\log n)^{3/2}$ in Ford's estimate. -/
noncomputable def growthDenominator446 (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ alpha446 *
    Real.log (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)

/-- Ford's growth rate $\frac{1}{(\log n)^\alpha (\log\log n)^{3/2}}$. -/
noncomputable def growth446 (n : ℕ) : ℝ :=
  (growthDenominator446 n)⁻¹

/-- $\delta_r(n)$, the density of the integers which have exactly $r$ divisors in $(n, 2n)$,
computed over one period as for `delta`. The values of $\delta_1(n)$ are recorded in OEIS
A399697 and A399698. -/
noncomputable def deltaR (r n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ divisorCount n m = r)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

/--
Let $\delta(n)$ denote the density of integers which are divisible by some integer in $(n,2n)$.
What is the growth rate of $\delta(n)$? If $\delta_1(n)$ is the density of integers which have
exactly one divisor in $(n,2n)$ then is it true that $\delta_1(n)=o(\delta(n))$?

Besicovitch [Be34] proved that $\liminf \delta(n)=0$. Erdős [Er35] proved that $\delta(n)=o(1)$.
Erdős [Er60] proved that $\delta(n)=(\log n)^{-\alpha+o(1)}$ where
$$\alpha=1-\frac{1+\log\log 2}{\log 2}=0.08607\cdots.$$
This estimate was refined by Tenenbaum [Te84], and the true growth rate of $\delta(n)$ was
determined by Ford [Fo08] who proved
$$\delta(n)\asymp \frac{1}{(\log n)^\alpha(\log\log n)^{3/2}}.$$
Erdős asked this at Oberwolfach in 1986, and wrote he was 'quite sure' that
$\delta_1(n)=o(\delta(n))$, but that 'recent results of Tenenbaum throw some doubt on this'.
Indeed, this was disproved by Ford [Fo08], who showed more generally that if $\delta_r(n)$ is the
density of integers with exactly $r$ divisors in $(n,2n)$ then $\delta_r(n)\gg_r\delta(n)$.

The statement below records all three results: Ford's growth rate, the lower bound
$\delta_r(n)\gg_r\delta(n)$ for every fixed $r\geq 1$, and the negative answer to the second
question.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos446.lean#L57"]
theorem erdos_446 :
    (delta =Θ[atTop] growth446) ∧
      (∀ r : ℕ, 1 ≤ r → delta =O[atTop] (deltaR r)) ∧
        ¬ (deltaR 1 =o[atTop] delta) := by
  sorry

/-- The second question on its own: is it true that $\delta_1(n)=o(\delta(n))$? Ford [Fo08]
proved that it is not. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos446.lean#L72"]
theorem erdos_446.variants.delta_one : answer(False) ↔ deltaR 1 =o[atTop] delta := by
  sorry

end Erdos446

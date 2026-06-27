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

import FormalConjectures.Util.ProblemImports

/-!
# Beck–Fiala theorem and conjecture

Discrepancy of bounded-degree set systems. Given sets $S_1, \dots, S_m \subseteq [n]$
such that every element of $[n]$ belongs to at most $t$ of the sets (the system has
*degree* at most $t$), one seeks a colouring $\chi \colon [n] \to \{-1, +1\}$ making
every set as balanced as possible, i.e. minimizing the *discrepancy*
$\max_i \left|\sum_{j \in S_i} \chi(j)\right|$.

The Beck–Fiala theorem (1981) states that every set system of degree at most $t \ge 1$
has discrepancy at most $2t - 1$. The Beck–Fiala conjecture asserts that the truth is
much stronger: the discrepancy of a degree-$t$ system is $O(\sqrt{t})$, with a constant
independent of $n$, $m$ and $t$.

Despite considerable attention the bound $2t - 1$ has been improved only slightly:
Bukh (2016) proved a bound of the form $2t - \log^* t$ (where $\log^*$ is the iterated
logarithm), and Banaszczyk's vector balancing theorem yields $O(\sqrt{t \log n})$.
The Komlós conjecture (see `KomlosConjecture.lean`) would imply the Beck–Fiala
conjecture, since scaling the incidence vectors of a degree-$t$ system by $1/\sqrt{t}$
produces vectors of Euclidean norm at most $1$.

*References:* 
- [Wikipedia](https://en.wikipedia.org/wiki/Beck%E2%80%93Fiala_theorem)
- [J. Beck and T. Fiala, *"Integer-making" theorems*,
  Discrete Applied Mathematics **3** (1981), 1–8](https://doi.org/10.1016/0166-218X(81)90022-6)
- [B. Bukh, *An improvement of the Beck–Fiala theorem*,
  Combinatorics, Probability and Computing **25** (2016), 380–398](https://doi.org/10.1017/S0963548315000140)
- [W. Banaszczyk, *Balancing vectors and Gaussian measures of n-dimensional convex bodies*,
  Random Structures & Algorithms **12** (1998), 351–360](https://doi.org/10.1002/(SICI)1098-2418(199807)12:4%3C351::AID-RSA3%3E3.0.CO;2-S)
-/

namespace BeckFiala

/--
**The Beck–Fiala theorem**

If $S_1, \dots, S_m \subseteq [n]$ is a set system of degree at most $t$, i.e. every
$j \in [n]$ lies in at most $t$ of the sets, and $t \ge 1$, then there is a colouring
$\chi \colon [n] \to \{-1, +1\}$ with $\left|\sum_{j \in S_i} \chi(j)\right| \le 2t - 1$
for every $i$.

The hypothesis $t \ge 1$ is necessary: a system of degree $0$ consists of empty sets
only, whose discrepancy is $0 > 2 \cdot 0 - 1$.

[J. Beck and T. Fiala, *"Integer-making" theorems*,
Discrete Applied Mathematics **3** (1981), 1–8.]
-/
@[category research solved, AMS 5]
theorem beck_fiala_theorem (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n))
    (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1 := by
  sorry

/--
**The Beck–Fiala conjecture**

There exists a universal constant $C > 0$ such that every set system
$S_1, \dots, S_m \subseteq [n]$ of degree at most $t$ admits a colouring
$\chi \colon [n] \to \{-1, +1\}$ with
$\left|\sum_{j \in S_i} \chi(j)\right| \le C \sqrt{t}$ for every $i$.
-/
@[category research open, AMS 5]
theorem beck_fiala_conjecture :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)),
      (∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) →
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
        ∀ i, |∑ j ∈ S i, χ j| ≤ C * Real.sqrt t := by
  sorry

/--
Sanity check: a system with no sets at all ($m = 0$) admits any colouring vacuously;
in particular the all-ones colouring satisfies every discrepancy bound.
-/
@[category test, AMS 5]
theorem beck_fiala_conjecture.variants.no_sets (n t : ℕ) (S : Fin 0 → Finset (Fin n))
    (_hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ Real.sqrt t :=
  ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => i.elim0⟩

end BeckFiala

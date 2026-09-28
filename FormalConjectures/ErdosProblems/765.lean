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
# Erdős Problem 765

*References:*
- [erdosproblems.com/765](https://www.erdosproblems.com/765)
- [Er38] Erdős, P., *On sequences of integers no one of which divides the product of two others
  and on related problems*. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.
- [Re58] Reiman, I., *Über ein Problem von K. Zarankiewicz*. Acta Math. Acad. Sci. Hungar. 9
  (1958), 269-273.
- [ERS66] Erdős, P. and Rényi, A. and Sós, V. T., *On a problem of graph theory*. Studia Sci. Math.
  Hungar. (1966), 215--235.
- [Br66] Brown, W. G., *On graphs that do not contain a Thomsen graph*. Canad. Math. Bull. (1966),
  281-285.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [Fu83] Füredi, Z., *Graphs without quadrilaterals*. J. Combin. Theory Ser. B 34 (1983),
  187-190.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [MaYa23] Ma, Jie and Yang, Tianchi, *Upper bounds on the extremal number of the 4-cycle*. Bull.
  Lond. Math. Soc. (2023), 1655--1667.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos765

/--
Give an asymptotic formula for $\mathrm{ex}(n; C_4)$.

Erdős and Klein [Er38] proved $\mathrm{ex}(n; C_4) \asymp n^{3/2}$, and Reiman [Re58] proved
$$\frac{1}{2\sqrt 2} \le \lim \frac{\mathrm{ex}(n; C_4)}{n^{3/2}} \le \frac12.$$
Erdős and Rényi [ERS66], and independently Brown [Br66], gave a construction showing that if
$n = q^2 + q + 1$ with $q$ a prime power then $\mathrm{ex}(n; C_4) \ge \frac12 q (q+1)^2$; together
with Reiman's upper bound this gives $\mathrm{ex}(n; C_4) \sim \frac12 n^{3/2}$. Füredi [Fu83] proved
$\mathrm{ex}(n; C_4) = \frac12 q (q+1)^2$ for $q > 13$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos765.lean#L24"]
theorem erdos_765 :
    (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ)) ~[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ) / 2 := by
  sorry

/--
Erdős [Er93] conjectured that $\mathrm{ex}(n; C_4) = \frac{n^{3/2}}{2} + \frac n4 + O(n^{1/2})$ for all
$n$, having proved the upper bound $\mathrm{ex}(n; C_4) \le \frac{n^{3/2}}{2} + \frac n4 + O(n^{1/2})$
in [Er75]. This is false: Ma and Yang [MaYa23] proved that, for some absolute constant $c > 0$ and
a positive density set of $n$, $\mathrm{ex}(n; C_4) \le \frac{n^{3/2}}{2} + (\frac14 - c) n$.
-/
@[category research solved, AMS 5]
theorem erdos_765.variants.second_term : answer(False) ↔
    (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) -
      (n : ℝ) ^ (3 / 2 : ℝ) / 2 - (n : ℝ) / 4) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos765

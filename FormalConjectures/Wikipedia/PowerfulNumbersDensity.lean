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
public import FormalConjectures.Millennium.RiemannHypothesis

/-!
# Asymptotic density of powerful numbers

Let $Q(x)$ denote the number of powerful integers up to $x$. Erdős and Szekeres [ES35] proved
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + O(x^{1/3}),$$
and Bateman and Grosswald [BG58] sharpened this to
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} + O(x^{1/6}).$$
Assuming the Riemann Hypothesis, H. Q. Liu improved the exponent $1/6$ to $121/860 + \varepsilon$
[SA26, §1]. The Riemann Hypothesis is now proved [Al26], which makes this improvement
unconditional.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Powerful_number)
- [ES35] Erdős, P. and Szekeres, G., *Über die Anzahl der Abelschen Gruppen gegebener Ordnung
  und über ein verwandtes zahlentheoretisches Problem*, Acta Sci. Math. (Szeged) 7 (1935), 95–102.
- [BG58] Bateman, P. T. and Grosswald, E., *On a theorem of Erdős and Szekeres*,
  Illinois J. Math. 2 (1958), 88–98.
- [SA26] Sankaranarayanan, A. and Akhilesh, P., *On the counting function of square-full numbers*,
  [arXiv:2609.02327](https://arxiv.org/abs/2609.02327) (2026).
- [Al26] Alpöge, L., [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf) (2026).
-/

@[expose] public section

open Filter Asymptotics Real

namespace PowerfulNumbersDensity

/-- $Q(x)$ is the number of powerful integers $n$ with $1 \le n \le x$. -/
noncomputable abbrev Q (x : ℝ) : ℕ := {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard

/-- The leading constant $\zeta(3/2)/\zeta(3) = 2.173\ldots$ -/
noncomputable abbrev A : ℝ := (riemannZeta (3 / 2)).re / (riemannZeta 3).re

/-- The second-order constant $\zeta(2/3)/\zeta(2)$, where $\zeta(2/3)$ is given by analytic
continuation. -/
noncomputable abbrev B : ℝ := (riemannZeta (2 / 3)).re / (riemannZeta 2).re

set_option linter.style.formal_proof_palomar false in
/--
Erdős and Szekeres [ES35] proved that the number of powerful integers up to $x$ satisfies
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + O(x^{1/3}).$$
In particular $Q(x) \sim \frac{\zeta(3/2)}{\zeta(3)} \sqrt{x}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-powerful-numbers/blob/775a39aa568faf06ceb598b585504af4d6fed303/PowerfulFC/Main.lean#L212"]
theorem asymptotic_erdos_szekeres :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 3) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Bateman and Grosswald [BG58] proved the sharper asymptotic
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} + O(x^{1/6}).$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-powerful-numbers/blob/775a39aa568faf06ceb598b585504af4d6fed303/PowerfulFC/BatemanGrosswald.lean#L358"]
theorem asymptotic_bateman_grosswald :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Can the exponent $1/6$ in the error term of the Bateman–Grosswald asymptotic be improved
unconditionally? That is, is there $\delta > 0$ such that
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} +
O(x^{1/6 - \delta})?$$
The answer is yes. Liu proved the exponent $121/860 + \varepsilon$ assuming the Riemann
Hypothesis [SA26, §1], and the Riemann Hypothesis is proved [Al26].
-/
@[category research solved, question, AMS 11,
  conditional formal_proof using lean4 at
    "https://github.com/ChironTheCentaur/rh-lab-powerful-numbers/blob/467faf0ee95603cd28ff806134bd3e0de330747d/PowerfulFC/ErrorTerm.lean#L236"
    assuming RiemannHypothesis.riemannHypothesis]
theorem error_term_improvement :
    ∃ δ > (0 : ℝ),
      (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
        fun x => x ^ ((1 : ℝ) / 6 - δ) := by
  sorry

end PowerfulNumbersDensity

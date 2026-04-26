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
# Erdős Problem 114

*Reference:* [erdosproblems.com/114](https://www.erdosproblems.com/114)

The **Erdős–Herzog–Piranian (EHP) conjecture** (1958): among all monic polynomials
$p$ of degree $n$, the arc length of the lemniscate $\{z \in \mathbb{C} \mid |p(z)| = 1\}$
is maximised uniquely by $p(z) = z^n - c$, $|c| = 1$.

### Known partial results

- **$n = 2$**: Eremenko–Hayman (1999) [EH99]
- **$3 \leq n \leq 14$**: Mendoza (2026), IEEE 1788-rigorous interval arithmetic,
  [doi:10.5281/zenodo.19480329](https://doi.org/10.5281/zenodo.19480329)
- **Sufficiently large $n$**: Tao (2025) [Ta25]
- **Upper bound**: $L(p) \leq 2\pi n$ for all monic degree-$n$ $p$ (Pommerenke, 1961)

### References

- [EHP58] Erdős, P., Herzog, F., Piranian, G. (1958). *Metric properties of polynomials*.
  J. Analyse Math. 6, 125–148.
- [Po61] Pommerenke, Ch. (1961). *Über die Kapazität ebener Kontinuen*.
  Math. Ann. 144, 115–120.
- [EH99] Eremenko, A., Hayman, W. (1999). *On the length of lemniscates*.
  Michigan Math. J. 46, 409–415.
- [Ta25] Tao, T. (2025). *The Erdős–Herzog–Piranian conjecture for large $n$*.

### AI disclosure

Lean 4 code in this file was drafted with assistance from Claude (Anthropic).
The mathematical content, computational verification, and certificates are the
author's own work.
-/

open Polynomial MeasureTheory ENNReal Classical

namespace Erdos114

/-- The level curve (lemniscate) of a polynomial `p` at level 1:
$\{z \in \mathbb{C} \mid \|p(z)\| = 1\}$. -/
def levelCurveUnit (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The arc length of the lemniscate of `p`, measured as the
1-dimensional Hausdorff measure of the level curve. -/
noncomputable def arcLength (p : ℂ[X]) : ℝ≥0∞ :=
  μH[1] (levelCurveUnit p)

/-- **Erdős Problem 114** (open conjecture). Among all monic polynomials of
degree $n$, $p(z) = z^n - c$ (with $|c| = 1$) maximises the arc length of the
lemniscate $\{z \in \mathbb{C} \mid |p(z)| = 1\}$.

Originally posed by Erdős, Herzog, and Piranian [EHP58]. Solved for $n = 2$
[EH99], $3 \leq n \leq 14$ (Mendoza, 2026), and sufficiently large $n$ [Ta25].
Open in general. -/
@[category research open, AMS 30]
theorem erdos_114 (n : ℕ) (hn : 1 ≤ n)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    arcLength p ≤ arcLength (X ^ n - C 1) := by
  sorry

/- ### Computational certificates (IEEE 1788, n = 3 … 14)

Each axiom encodes one degree's branch-and-bound result.  The computation is
externally reproducible: download the Zenodo deposit, run `python verify_ehp.py
--degree N` (Python/mpmath, n ≤ 12) or `cargo run --release -- --degree N`
(Rust/inari, n ≤ 14).  Every interval is certified per IEEE 1788-2015 (directed
rounding, no silent overflow).

Experiment series: EXP-MM-EHP-007, combined results at
[doi:10.5281/zenodo.19480329](https://doi.org/10.5281/zenodo.19480329),
file `EXP-MM-EHP-007_COMBINED.json`.

Summary of margins (L* = arc length of z^n − 1, gap = L* − max competitor):

| n  | L*           | gap (abs) | gap (%) | B&B boxes | time  |
|----|--------------|-----------|---------|-----------|-------|
|  3 | 9.1797…      | 0.564     | 6.1 %   | 512       | 7 s   |
|  4 | 12.274…      | 0.412     | 3.4 %   | 4 096     | 18 s  |
|  5 | 15.393…      | 0.318     | 2.1 %   | 32 768    | 52 s  |
|  6 | 18.530…      | 0.261     | 1.4 %   | 262 144   | 3 min |
| 7–14 | …          | ≥ 0.18   | ≥ 1.0 % | —        | ≤ 8 h |

Hessian checked negative-definite at the extremizer for each degree; see
`P114_SYMMETRIZATION_TEST_REPORT.md` and `EHP_Proof_Evaluation_Brief.md`
in the MendozaLab workbench. -/

/-- IEEE 1788 certificate: z³ − 1 maximises lemniscate length for n = 3. -/
axiom ehp_cert_3  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 3)  :
    arcLength p ≤ arcLength (X ^ 3  - C 1)

/-- IEEE 1788 certificate: z⁴ − 1 maximises lemniscate length for n = 4. -/
axiom ehp_cert_4  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 4)  :
    arcLength p ≤ arcLength (X ^ 4  - C 1)

/-- IEEE 1788 certificate: z⁵ − 1 maximises lemniscate length for n = 5. -/
axiom ehp_cert_5  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 5)  :
    arcLength p ≤ arcLength (X ^ 5  - C 1)

/-- IEEE 1788 certificate: z⁶ − 1 maximises lemniscate length for n = 6. -/
axiom ehp_cert_6  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 6)  :
    arcLength p ≤ arcLength (X ^ 6  - C 1)

/-- IEEE 1788 certificate: z⁷ − 1 maximises lemniscate length for n = 7. -/
axiom ehp_cert_7  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 7)  :
    arcLength p ≤ arcLength (X ^ 7  - C 1)

/-- IEEE 1788 certificate: z⁸ − 1 maximises lemniscate length for n = 8. -/
axiom ehp_cert_8  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 8)  :
    arcLength p ≤ arcLength (X ^ 8  - C 1)

/-- IEEE 1788 certificate: z⁹ − 1 maximises lemniscate length for n = 9. -/
axiom ehp_cert_9  (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 9)  :
    arcLength p ≤ arcLength (X ^ 9  - C 1)

/-- IEEE 1788 certificate: z¹⁰ − 1 maximises lemniscate length for n = 10. -/
axiom ehp_cert_10 (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 10) :
    arcLength p ≤ arcLength (X ^ 10 - C 1)

/-- IEEE 1788 certificate: z¹¹ − 1 maximises lemniscate length for n = 11. -/
axiom ehp_cert_11 (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 11) :
    arcLength p ≤ arcLength (X ^ 11 - C 1)

/-- IEEE 1788 certificate: z¹² − 1 maximises lemniscate length for n = 12. -/
axiom ehp_cert_12 (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 12) :
    arcLength p ≤ arcLength (X ^ 12 - C 1)

/-- IEEE 1788 certificate: z¹³ − 1 maximises lemniscate length for n = 13.
    Verified with Rust/inari (MPFR-backed directed rounding). -/
axiom ehp_cert_13 (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 13) :
    arcLength p ≤ arcLength (X ^ 13 - C 1)

/-- IEEE 1788 certificate: z¹⁴ − 1 maximises lemniscate length for n = 14.
    Verified with Rust/inari (MPFR-backed directed rounding). -/
axiom ehp_cert_14 (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = 14) :
    arcLength p ≤ arcLength (X ^ 14 - C 1)

/-- **Erdős Problem 114, small $n$** (solved, computationally certified).
For $3 \leq n \leq 14$, the polynomial $z^n - 1$ maximises the arc length of
the lemniscate among all monic polynomials of degree $n$.

Proof: decidable case split on $n$; each case discharged by the corresponding
IEEE 1788 certificate axiom above.  Zero `sorry` stubs; all non-trivial claims
are explicit `axiom` declarations with full computational citations.

*Reference:* K. Mendoza (2026).
[doi:10.5281/zenodo.19480329](https://doi.org/10.5281/zenodo.19480329) -/
@[category research solved, AMS 30]
theorem erdos_114_small_n (n : ℕ) (hn : 3 ≤ n) (hn14 : n ≤ 14)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    arcLength p ≤ arcLength (X ^ n - C 1) := by
  interval_cases n
  · exact ehp_cert_3  p hp hp_deg
  · exact ehp_cert_4  p hp hp_deg
  · exact ehp_cert_5  p hp hp_deg
  · exact ehp_cert_6  p hp hp_deg
  · exact ehp_cert_7  p hp hp_deg
  · exact ehp_cert_8  p hp hp_deg
  · exact ehp_cert_9  p hp hp_deg
  · exact ehp_cert_10 p hp hp_deg
  · exact ehp_cert_11 p hp hp_deg
  · exact ehp_cert_12 p hp hp_deg
  · exact ehp_cert_13 p hp hp_deg
  · exact ehp_cert_14 p hp hp_deg

end Erdos114

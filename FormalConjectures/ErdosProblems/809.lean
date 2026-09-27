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
# Erdős Problem 809

*References:*
- [erdosproblems.com/809](https://www.erdosproblems.com/809)
- [BEGS89] Burr, S. A., Erdős, P., Graham, R. L. and Sós, V. T., *Maximal antiramsey graphs and
  the strong chromatic number*. J. Graph Theory (1989), 263-282.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [BCM26] Bucić, M., Chen, K. and Ma, J., *On a maximal anti-Ramsey conjecture of Burr, Erdős,
  Graham, and Sós*. arXiv:2603.18952 (2026).
- [Sh26] Shahab, A., *The Burr–Erdős–Graham–Sós conjecture for the seven-cycle* (2026).
  [PDF](https://github.com/Asad-Shahab/erdos-809-lean/blob/main/paper/erdos809_manuscript.pdf)
-/

@[expose] public section

namespace Erdos809

open SimpleGraph Filter Asymptotics

/--
$\chi_S(n, e, H)$ is the least $r$ such that some graph with $n$ vertices and $e$ edges has an
edge colouring with $r$ colours in which every copy of $H$ has distinct edge colours.
-/
noncomputable def strongChromaticNum {α : Type*} (H : SimpleGraph α) (n e : ℕ) : ℕ :=
  sInf {r | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
    ∃ c : G.EdgeLabeling (Fin r), ∀ f : H.Copy G, IsRainbow f.toHom c}

/--
Is it true that, for all $k \geq 3$,
$$\chi_S(n, \lfloor n^2/4 \rfloor + 1, C_{2k+1}) \sim \frac{n^2}{8}?$$

Bucić, Chen, and Ma [BCM26] proved this for all $k \geq 4$, and Shahab [Sh26] proved the case
$k = 3$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/Asad-Shahab/erdos-809-lean/blob/7ec4aaa6e9d685e8f9948005d8be69923cce2ab8/Erdos809/OddCycles.lean#L11"]
theorem erdos_809 : answer(True) ↔ ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := by
  sorry

/--
Burr, Erdős, Graham, and Sós [BEGS89] proved that
$\chi_S(n, \lfloor n^2/4 \rfloor + 1, C_{2k+1}) \gg_k n^2$ for every $k \geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.burr_erdos_graham_sos (k : ℕ) (hk : 3 ≤ k) :
    ∃ c > (0 : ℝ), ∀ᶠ n in atTop,
      c * n ^ 2 ≤ strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) := by
  sorry

/--
Bucić, Chen, and Ma [BCM26] proved that
$\chi_S(n, \lfloor n^2/4 \rfloor + 1, C_{2k+1}) \sim n^2/8$ for every $k \geq 4$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/Asad-Shahab/erdos-809-lean/blob/7ec4aaa6e9d685e8f9948005d8be69923cce2ab8/Erdos809/LongOddCycles/Main.lean#L54"]
theorem erdos_809.variants.bucic_chen_ma (k : ℕ) (hk : 4 ≤ k) :
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := by
  sorry

/--
Shahab [Sh26] proved that $\chi_S(n, \lfloor n^2/4 \rfloor + 1, C_7) \sim n^2/8$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/Asad-Shahab/erdos-809-lean/blob/7ec4aaa6e9d685e8f9948005d8be69923cce2ab8/Erdos809/Main.lean#L40"]
theorem erdos_809.variants.seven_cycle :
    (fun n ↦ (strongChromaticNum (cycleGraph 7) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := by
  sorry

/--
Erdős and Simonovits proved (as reported in [BEGS89]) that
$\chi_S(n, \lfloor n^2/4 \rfloor + 1, C_5) = \lfloor n/2 \rfloor + 3$ for all large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_809.variants.five_cycle :
    ∀ᶠ n in atTop, strongChromaticNum (cycleGraph 5) n (n ^ 2 / 4 + 1) = n / 2 + 3 := by
  sorry

end Erdos809

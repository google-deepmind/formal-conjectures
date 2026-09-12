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

import FormalConjecturesUtil

/-!
# Erdős Problem 571

*References:*
- [erdosproblems.com/571](https://www.erdosproblems.com/571)
- [BuCo18] Bukh, Boris and Conlon, David, *Rational exponents in extremal graph theory*. J. Eur.
  Math. Soc. (JEMS) (2018), 1747-1757.
- [CJL21] Conlon, David and Janzer, Oliver and Lee, Joonkyung, *More on the extremal number of
  subdivisions*. Combinatorica (2021), 465-494.
- [CoJa22] Conlon, David and Janzer, Oliver, *Rational exponents near two*. Adv. Comb. (2022), Paper
  No. 9, 10.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [JJM20] Jiang, Tao and Jiang, Zilin and Ma, Jie, *Negligible obstructions and Turán exponents*.
  arXiv:2007.02975 (2020).
- [JMY22] Jiang, Tao and Ma, Jie and Yepremyan, Liana, *On Turán exponents of bipartite graphs*.
  Combin. Probab. Comput. (2022), 333-344.
- [JiQi20] Jiang, Tao and Qiu, Yu, *Turán numbers of bipartite subdivisions*. SIAM J. Discrete Math.
  (2020), 556-570.
- [JiQi23] Jiang, Tao and Qiu, Yu, *Many Turán exponents via subdivisions*. Combin. Probab. Comput.
  (2023), 134-150.
- [KKL21] Kang, Dong Yeap and Kim, Jaehoon and Liu, Hong, *On the rational Turán exponents
  conjecture*. J. Combin. Theory Ser. B (2021), 149-172.
-/

open Filter SimpleGraph

namespace Erdos571

/--
Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that $$\mathrm{ex}(n;G)\asymp n^{\alpha}.$$
-/
@[category research open, AMS 5]
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ)) := by
  sorry

end Erdos571

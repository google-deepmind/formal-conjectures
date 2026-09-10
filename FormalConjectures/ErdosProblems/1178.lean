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
# Erdős Problem 1178

*References:*
- [erdosproblems.com/1178](https://www.erdosproblems.com/1178)
- [BES73] Brown, W. G. and Erdős, P. and S\'os, V. T., Some extremal problems on {$r$}-graphs.
(1973), 53--63.
- [CGLS23] Conlon, David and Gishboliner, Lior and Levanzov, Yevgeny and Shapira, Asaf, A new bound
for the {B}rown-{E}rd\H os-S\'os problem. J. Combin. Theory Ser. B (2023), 1--35.
- [EFR86] Erdős, P. and Frankl, P. and Rödl, V., The asymptotic number of graphs not containing a
fixed subgraph and a problem for hypergraphs having no exponent. Graphs Combin. (1986), 113-121.
- [Er75b] Erdős, Paul, Problems and results in combinatorial number theory. Journ\'{e}es
Arithm\'{e}tiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [RuSz78] Ruzsa, I. Z. and Szemer\'{e}di, E., Triple systems with no six points carrying three
triangles. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978), 939-945.
- [SaSe05] Sárk\"ozy, Gábor N. and Selkow, Stanley, An extension of the {R}uzsa-Szemer\'edi theorem
. Combinatorica (2005), 77--84.
- [SoSo17] Solymosi, David and Solymosi, Jozsef, Small cores in 3-uniform hypergraphs. J. Combin.
Theory Ser. B (2017), 897--910.
-/

namespace Erdos1178

open Filter Asymptotics

/--
For $r\geq 3$ let $d_r(e)$ be the minimal $d$ such that
$$\mathrm{ex}_r(n,\mathcal{F})=o(n^2),$$
where $\mathcal{F}$ is the family of $r$-uniform hypergraphs on $d$ vertices with $e$ edges. Prove
that
$$d_r(e)=(r-2)e+3$$
for all $r,e\geq 3$.
-/
@[category research open, AMS 5]
theorem erdos_1178 :
    ∀ r e : ℕ, 3 ≤ r → 3 ≤ e →
    Hypergraph.sparseConfigurationThreshold r e = (((r - 2) * e + 3 : ℕ) : ℕ∞) := by
  sorry

end Erdos1178

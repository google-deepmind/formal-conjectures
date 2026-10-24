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
# Erdős Problem 492

*References:*
- [erdosproblems.com/492](https://www.erdosproblems.com/492)
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*.
  Compositio Math. 16 (1964), 52–65, §IV.4, p. 62.
  [Original paper](https://www.numdam.org/item/CM_1964__16__52_0.pdf).
- [DaEr63] Davenport, H. and Erdős, P., *A theorem on uniform distribution*.
  Publ. Math. Inst. Hungar. Acad. Sci. 8 (1963), 3–11.
  [Original paper](https://www.renyi.hu/~p_erdos/1963-01.pdf).
- [Er75] Erdős, P., *Problems and results on diophantine approximations (II)*.
  (1975), 89–99, §5, p. 94.
  [Original paper](https://www.renyi.hu/~p_erdos/1975-31.pdf).
- [Sc69] Schmidt, W. M., *Disproof of some conjectures on Diophantine approximations*.
  Studia Sci. Math. Hungar. 4 (1969), 137–144.
-/

@[expose] public section

namespace Erdos492

open SubdivisionDistribution

/--
Let $a_1<a_2<\cdots$ be positive real numbers tending to infinity, with
$a_{i+1}/a_i\to 1$. For $x\in[a_i,a_{i+1})$, put
$f(x)=(x-a_i)/(a_{i+1}-a_i)$. Is it true that, for almost all $\alpha>0$,
$f(\alpha n)$ is uniformly distributed in $[0,1)$?

The general conjecture is false, as shown by Schmidt [Sc69], as reported in
[Er75, §5]. The real boundary domain follows [Er64b] and [DaEr63].
The website specifies natural boundaries; that restriction is handled separately
in `erdos_492.variants.natural_boundaries`.
-/
@[category research solved, AMS 11 28]
theorem erdos_492 : answer(False) ↔ RealSubdivision.HistoricalRealQuestion := by
  sorry

/--
For increasing natural boundaries $a_i$ with $a_{i+1}/a_i\to 1$, is
$f(\alpha n)$ uniformly distributed in $[0,1)$ for almost all $\alpha>0$?

This is the website's literal domain. Its affirmative answer follows from
[DaEr63]: there are at most $N$ boundaries below $N$, so the sparse-boundary
hypothesis holds with $\delta=1$. The reduction is proved by
`SubdivisionDistribution.natQuestion_of_davenportErdos`; the analytic theorem
it uses is not proved here.
-/
@[category research solved, AMS 11 28]
theorem erdos_492.variants.natural_boundaries : answer(True) ↔ NatQuestion := by
  sorry

/--
Davenport and Erdős [DaEr63] proved almost-everywhere uniform distribution when
$X(N)\ll N^{2-\delta}$ for some fixed $\delta>0$, where $X(N)$ counts the
subdivision boundaries below $N$.
-/
@[category research solved, AMS 11 28]
theorem erdos_492.variants.sparse_boundaries : RealSubdivision.DavenportErdosStatement := by
  sorry

end Erdos492

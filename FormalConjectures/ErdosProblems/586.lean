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
# Erdős Problem 586

*References:*
- [erdosproblems.com/586](https://www.erdosproblems.com/586)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [Er96b] Erdős, Paul, _Some problems I presented or planned to present in my short talk_.
  Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333-335.
- [Er97] Erdős, Paul, _Problems in number theory_. New Zealand J. Math. (1997), 155-160.
- [Er97c] Erdős, Paul, _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Er97e] Erdős, Paul, _Some of my favourite unsolved problems_. Math. Japon. (1997), 527-537.
- [BBMST22] Balister, Paul and Bollobás, Béla and Morris, Robert and Sahasrabudhe, Julian and
  Tiba, Marius, _On the Erdős covering problem: the density of the uncovered set_. Invent. Math.
  (2022), 377-414.
-/

@[expose] public section

namespace Erdos586

/--
Is there a covering system such that no two of the moduli divide each other?

Asked by Schinzel, motivated by a question of Erdős and Selfridge (see
[7](https://www.erdosproblems.com/7)). The answer is no, as proved by Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22].

The moduli of a `CoveringSystem ℤ` are the ideals $(m_i)$; the modulus $m_i$ divides $m_j$
exactly when $(m_j)\subseteq (m_i)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos586.lean#L186"]
theorem erdos_586 : answer(False) ↔
    ∃ c : CoveringSystem ℤ, Pairwise fun i j ↦ ¬ c.moduli j ≤ c.moduli i := by
  sorry

end Erdos586

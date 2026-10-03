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
# Erdős Problem 557

*References:*
- [erdosproblems.com/557](https://www.erdosproblems.com/557)
- [ErGr75] Erdős, P. and Graham, R. L., *On partition theorems for finite graphs*. Infinite and
  finite sets (Colloq., Keszthely, 1973), Vol. I, Colloq. Math. Soc. János Bolyai 10 (1975),
  515-527.
- [ReSt26] Reed, Bruce and Stein, Maya, *The Erdős-Sós conjecture in dense graphs*.
  [arXiv:2609.05417](https://arxiv.org/abs/2609.05417) (2026).
-/

open SimpleGraph

namespace Erdos557

/--
Let $R_k(G)$ denote the minimal $m$ such that if the edges of $K_m$ are $k$-coloured then there
is a monochromatic copy of $G$. Is it true that
$$R_k(T)\leq kn+O(1)$$
for any tree $T$ on $n$ vertices?

The answer is yes, with an absolute constant: $R_k(T) \leq k(n-2)+3 \leq kn + 3$ for all $k$
and $n$. This follows from the Erdős–Sós theorem (Erdős problem 548) by the pigeonhole principle,
as recorded on the problem page; Reed and Stein [ReSt26] derived it for $n$ large in terms of $k$
from their dense-graph case of Erdős–Sós.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/zhangjun725/erdos557/blob/c4e0ab13027f8bb50defade11cf8a53c7b8b0ba9/Erdos557/Basic.lean#L153"]
theorem erdos_557 :
    ∃ c : ℕ, ∀ (k n : ℕ) (T : SimpleGraph (Fin n)), T.IsTree →
      multicolourGraphRamsey k T ≤ k * n + c := by
  sorry

/--
The explicit bound $R_k(T) \leq k(n-2)+3$ for every tree $T$ on $n$ vertices and every $k$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/zhangjun725/erdos557/blob/c4e0ab13027f8bb50defade11cf8a53c7b8b0ba9/Erdos557/Basic.lean#L147"]
theorem erdos_557.variants.explicit (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    multicolourGraphRamsey k T ≤ k * (n - 2) + 3 := by
  sorry

/--
The best-possible bound $R_k(T) \leq k(n-2)+2$ for every $k$ and every tree $T$ on $n \geq 2$
vertices, attained by stars. It follows from the sharp form of the Erdős–Sós theorem (a graph on
$m$ vertices with more than $(n-2)m/2$ edges contains every tree on $n$ vertices) by the
pigeonhole principle.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/zhangjun725/erdos557/blob/828ad6fdb5d0f1a72b8dcd812f4c91c285570ff6/Erdos557/Tight.lean#L108"]
theorem erdos_557.variants.tight (k n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : multicolourGraphRamsey k T ≤ k * (n - 2) + 2 := by
  sorry

/--
When $n$ is odd and $k \geq 2$ is even, $R_k(T) \leq k(n-2)+1$ for every tree $T$ on $n$ vertices,
again attained by stars: with $m = k(n-2)+1$ some colour class has at least $(n-2)m/2$ edges, and
$(n-2)m$ is odd, so it has more than $(n-2)m/2$ edges.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/zhangjun725/erdos557/blob/828ad6fdb5d0f1a72b8dcd812f4c91c285570ff6/Erdos557/Tight.lean#L114"]
theorem erdos_557.variants.tight_odd (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n)
    (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    multicolourGraphRamsey k T ≤ k * (n - 2) + 1 := by
  sorry

end Erdos557

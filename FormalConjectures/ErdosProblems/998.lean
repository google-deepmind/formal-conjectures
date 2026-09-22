/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 998

*References:*
- [erdosproblems.com/998](https://www.erdosproblems.com/998)
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math.
  (1964), 52-65.
- [He22] Hecke, E., *Über analytische Funktionen und die Verteilung von Zahlen mod. eins*. Abh.
  Math. Sem. Univ. Hamburg (1922), 54--76.
- [Os27] Ostrowski, Alexander, *Mathematische Miszellen. IX. Notiz zur Theorie der Diophantischen
  Approximationen*. Jber. Deutsch. Math.-Verein. (1927), 178-180.
- [Os30] Ostrowski, Alexander, *Mathematische Miszellen. XVI. Zur Theorie der linearen
  Diophantischen Approximationen*. Jber. Deutsch. Math.-Verein. (1930), 34-46.
- [Ke66] Kesten, Harry, *On a conjecture of Erdős and Szüsz related to uniform distribution
  mod $1$*. Acta Arith. (1966/67), 193--212.
-/

@[expose] public section

open Filter

namespace Erdos998

/-- The interval $[u, v)$ has bounded remainder for $\alpha$: for all large $n$,
$\#\{ 1\leq m\leq n : \{ \alpha m\} \in [u,v)\} = n(v-u)+O(1)$. -/
def HasBoundedRemainder (α u v : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    |(((Finset.Icc 1 n).filter fun m : ℕ => Int.fract (α * m) ∈ Set.Ico u v).card : ℝ) -
      n * (v - u)| ≤ C

/--
Let $\alpha$ be an irrational number. Is it true that if, for all large $n$,
$$\#\{ 1\leq m\leq n : \{ \alpha m\} \in [u,v)\} = n(v-u)+O(1)$$
then $u=\{\alpha k\}$ and $v=\{\alpha \ell\}$ for some integers $k$ and $\ell$?

A problem of Erdős and Szüsz. Hecke [He22] and Ostrowski ([Os27] and [Os30]) proved the
converse. This is true, and was proved by Kesten [Ke66].

As literally stated the conclusion is too strong: Kesten's theorem says that $[u, v)$ has bounded
remainder if and only if $v - u \in \mathbb{Z}\alpha + \mathbb{Z}$, which does not constrain $u$
itself (for instance $u = 1/4$, $v = 1/4 + \sqrt{2}/10$, $\alpha = \sqrt{2}/10$); see
`erdos_998.variants.kesten` for the correct statement.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos998.lean#L260"]
theorem erdos_998 : answer(False) ↔ ∀ α u v : ℝ, Irrational α → 0 ≤ u → u < v → v ≤ 1 →
    HasBoundedRemainder α u v →
      (∃ k : ℤ, u = Int.fract (α * k)) ∧ ∃ l : ℤ, v = Int.fract (α * l) := by
  sorry

/--
Kesten's theorem [Ke66] (with the converse of Hecke [He22] and Ostrowski [Os27], [Os30]): for
irrational $\alpha$ and $0 \leq u < v \leq 1$, the interval $[u, v)$ has bounded remainder if and
only if $v - u = \{k\alpha\}$ for some integer $k$, or $v - u = 1$.
-/
@[category research solved, AMS 11]
theorem erdos_998.variants.kesten (α u v : ℝ) (hα : Irrational α) (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ 1) :
    HasBoundedRemainder α u v ↔ (∃ k : ℤ, v - u = Int.fract (α * k)) ∨ v - u = 1 := by
  sorry

end Erdos998

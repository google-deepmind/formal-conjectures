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
# Erdős Problem 83

*References:*
- [erdosproblems.com/83](https://www.erdosproblems.com/83)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44-48.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [ErKoRa61] Erdős, P. and Ko, Chao and Rado, R., *Intersection theorems for systems of finite
  sets*. Quart. J. Math. Oxford Ser. (2) (1961), 313-320.
- [AhKh97] Ahlswede, Rudolf and Khachatrian, Levon H., *The complete intersection theorem for
  systems of finite sets*. European J. Combin. (1997), 125-136.
-/

@[expose] public section

namespace Erdos83

/--
Suppose that we have a family $\mathcal{F}$ of subsets of $[4n]$ such that $\lvert A\rvert=2n$
for all $A\in\mathcal{F}$ and for every $A,B\in \mathcal{F}$ we have
$\lvert A\cap B\rvert \geq 2$. Then
$$\lvert \mathcal{F}\rvert \leq \frac{1}{2}\left(\binom{4n}{2n}-\binom{2n}{n}^2\right).$$

Conjectured by Erdős, Ko, and Rado [ErKoRa61]. This inequality would be best possible, as shown
by taking $\mathcal{F}$ to be the collection of all subsets of $[4n]$ of size $2n$ containing at
least $n+1$ elements from $[2n]$.

Proved by Ahlswede and Khachatrian [AhKh97], who more generally showed the following. Let
$2\leq t\leq k\leq m$ and let $r\geq 0$ be such that
$$\frac{1}{r+1}\leq \frac{m-2k+2t-2}{(t-1)(k-t+1)}< \frac{1}{r}.$$
The largest possible family of subsets of $[m]$ of size $k$, such that the pairwise
intersections have size at least $t$, is the family of all subsets of $[m]$ of size $k$ which
contain at least $t+r$ elements from $\{1,\ldots,t+2r\}$.

The number $\binom{4n}{2n}-\binom{2n}{n}^2$ is even, so the bound is an integer.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos83.lean#L36"]
theorem erdos_83 (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 := by
  sorry

/--
The bound in [erdős_83](https://www.erdosproblems.com/83) is attained by the family of all
subsets of $[4n]$ of size $2n$ containing at least $n+1$ elements from $[2n]$.
-/
@[category research solved, AMS 5]
theorem erdos_83.variants.extremal (n : ℕ) :
    ∃ F : Finset (Finset (Fin (4 * n))), (∀ A ∈ F, A.card = 2 * n) ∧
      (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ∧
      F.card = ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 := by
  sorry

/--
The complete intersection theorem of Ahlswede and Khachatrian [AhKh97]: for $2\leq t\leq k\leq m$,
every family of $k$-subsets of $[m]$ with pairwise intersections of size at least $t$ is at most
as large as one of the families of all $k$-subsets of $[m]$ containing at least $t+r$ elements of
$\{1,\ldots,t+2r\}$, $r \geq 0$.
-/
@[category research solved, AMS 5]
theorem erdos_83.variants.ahlswede_khachatrian (m k t : ℕ) (ht : 2 ≤ t) (htk : t ≤ k)
    (hkm : k ≤ m) (F : Finset (Finset (Fin m))) (hF : ∀ A ∈ F, A.card = k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, t ≤ (A ∩ B).card) :
    ∃ r : ℕ, F.card ≤ ({A : Finset (Fin m) | A.card = k ∧
      t + r ≤ (A.filter fun i : Fin m => (i : ℕ) < t + 2 * r).card} : Finset _).card := by
  sorry

end Erdos83

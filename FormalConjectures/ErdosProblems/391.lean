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
# Erdős Problem 391

*References:*
- [erdosproblems.com/391](https://www.erdosproblems.com/391)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er96b] Erdős, Paul, *Some problems I presented or planned to present in my short talk*.
  Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333-335.
- [AlGr77] Alladi, Krishnaswami and Grinstead, Charles, *On the decomposition of $n!$ into prime
  powers*. J. Number Theory (1977), 452-458.
- [ACRSTUV25] B. Alexeev, E. Conway, M. Rosenfeld, A. Sutherland, T. Tao, M. Uhr, and K.
  Ventullo, *Decomposing a factorial into large factors*. arXiv:2503.20170 (2025).
-/

@[expose] public section

open Filter Topology

namespace Erdos391

/-- `t n` is the largest `t` such that `n!` is a product of `n` factors all at least `t`,
i.e. the maximal $a_1$ in a representation $n! = a_1 \cdots a_n$ with $a_1 \leq \cdots \leq a_n$. -/
noncomputable def t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin n → ℕ, ∏ i, a i = n.factorial ∧ ∀ i, k ≤ a i}

/--
Let $t(n)$ be maximal such that there is a representation
$$n!=a_1\cdots a_n$$
with $t(n)=a_1\leq \cdots \leq a_n$. Obtain good bounds for $t(n)/n$. In particular, is it true
that
$$\lim \frac{t(n)}{n}=\frac{1}{e}?$$

It is easy to see that $\lim \frac{t(n)}{n}\leq \frac{1}{e}$. Erdős [Er96b] wrote he, Selfridge,
and Straus had proved a corresponding lower bound, so that $\lim \frac{t(n)}{n}=\frac{1}{e}$, and
'believed that Straus had written up our proof. Unfortunately Straus suddenly died and no trace
was ever found of his notes. Furthermore, we never could reconstruct our proof, so our assertion
now can be called only a conjecture.'

Alladi and Grinstead [AlGr77] have obtained similar results when the $a_i$ are restricted to
prime powers.

Both questions were answered by Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, and Ventullo
[ACRSTUV25], who proved that
$$\frac{t(n)}{n}= \frac{1}{e}-\frac{c_0}{\log n}+O\left(\frac{1}{(\log n)^{1+c}}\right),$$
where $c_0=0.3044\cdots$ is an explicit constant, for some $c>0$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos391.lean#L4924"]
theorem erdos_391 : answer(True) ↔
    Tendsto (fun n : ℕ => (t n : ℝ) / n) atTop (𝓝 (1 / Real.exp 1)) := by
  sorry

/--
Furthermore, does there exist some constant $c>0$ such that
$$\frac{t(n)}{n} \leq \frac{1}{e}-\frac{c}{\log n}$$
for infinitely many $n$?

This was answered in the affirmative by Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, and
Ventullo [ACRSTUV25].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos391.lean#L4924"]
theorem erdos_391.variants.deficit : answer(True) ↔ ∃ c : ℝ, 0 < c ∧
    {n : ℕ | (t n : ℝ) / n ≤ 1 / Real.exp 1 - c / Real.log n}.Infinite := by
  sorry

end Erdos391

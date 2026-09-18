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
# Erdős Problem 1005

*References:*
- [erdosproblems.com/1005](https://www.erdosproblems.com/1005)
- [Ma42] Mayer, A. E., *A mean value theorem concerning Farey series*. Quart. J. Math. Oxford
  Ser. (1942), 48-57.
- [Er43] Erdős, P., *A note on Farey series*. Quart. J. Math. Oxford Ser. (1943), 82-85.
- [vD25b] van Doorn, W., *Improved bounds for the Mayer-Erdős phenomenon on similarly ordered Farey
  fractions*. [arXiv:2509.00121](https://arxiv.org/abs/2509.00121) (2025).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos1005

/-- A rational `q` is a Farey fraction of order `n` if it lies in `[0, 1]` and has denominator at
most `n`. (Every `q : ℚ` is stored in lowest terms, so `q.den` and `q.num` are the reduced
denominator and numerator.) -/
def IsFarey (n : ℕ) (q : ℚ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of Farey fractions of order `n` strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- `f n` is the largest integer such that any two Farey fractions of order `n` whose indices
differ by at most `f n` are similarly ordered: it is the minimum, over all pairs `x < y` of Farey
fractions of order `n` with `(x.num - y.num) * (x.den - y.den) < 0`, of the number of Farey
fractions strictly between `x` and `y`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ x y : ℚ, IsFarey n x ∧ IsFarey n y ∧ x < y ∧
    (x.num - y.num) * ((x.den : ℤ) - y.den) < 0 ∧ betweenCount n x y = k}

/--
Let $\frac{a_1}{b_1}, \frac{a_2}{b_2}, \ldots$ be the Farey fractions of order $n \geq 4$. Let
$f(n)$ be the largest integer such that if $1 \leq k < l \leq k + f(n)$ then $\frac{a_k}{b_k}$ and
$\frac{a_l}{b_l}$ are similarly ordered, in other words $(a_k - a_l)(b_k - b_l) \geq 0$. Estimate
$f(n)$: in particular, is there a constant $c > 0$ such that $f(n) = (c + o(1)) n$ for all
large $n$?

Mayer [Ma42] proved that $f(n) \to \infty$ and Erdős [Er43] that $f(n) \gg n$. Van Doorn [vD25b]
proved $(1/12 - o(1)) n \le f(n) \le n / 4 + O(1)$ and conjectured that $f(n) = (1/4 + o(1)) n$,
which was proved by Cipollini and GPT-5.5; see `erdos_1005.variants.constant`.
-/
@[category research solved, AMS 11]
theorem erdos_1005 : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 c) := by
  sorry

/-- The constant in Problem 1005 is $c = 1/4$: $f(n) = (1/4 + o(1)) n$ (Cipollini and GPT-5.5;
formalised by Cipollini, van Doorn and Aristotle). -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1005.lean#L44"]
theorem erdos_1005.variants.constant :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 (1 / 4)) := by
  sorry

end Erdos1005

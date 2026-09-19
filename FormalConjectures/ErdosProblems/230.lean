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
# Erdős Problem 230

*References:*
- [erdosproblems.com/230](https://www.erdosproblems.com/230)
- [Er57] Erdős, Paul, *Some unsolved problems*. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
- [Er80h] Erdős, P., *Problems and results on polynomials and interpolation*. (1980), 383--391.
- [Ko80] Körner, T. W., *On a polynomial of Byrnes*. Bull. London Math. Soc. (1980), 219--224.
- [Ka80] Kahane, Jean-Pierre, *Sur les polynômes à coefficients unimodulaires*. Bull. London Math.
  Soc. (1980), 321-342.
- [BoBo09] Bombieri, Enrico and Bourgain, Jean, *On Kahane's ultraflat polynomials*. J. Eur. Math.
  Soc. (JEMS) (2009), 627-703.
-/

@[expose] public section

open Filter Topology

namespace Erdos230

/-- The maximum of $\lvert P(z)\rvert$ over the unit circle, for
$P(z)=\sum_{1\leq k\leq n}a_kz^k$. -/
noncomputable def circleMax {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖∑ k : Fin n, a k * (z : ℂ) ^ ((k : ℕ) + 1)‖

/--
Let $P(z)=\sum_{1\leq k\leq n}a_kz^k$ for some $a_k\in \mathbb{C}$ with $\lvert a_k\rvert=1$ for
$1\leq k\leq n$. Does there exist a constant $c>0$ such that, for $n\geq 2$, we have
$$\max_{\lvert z\rvert=1}\lvert P(z)\rvert \geq (1+c)\sqrt{n}?$$

This is Problem 4.31 in [Ha74], in which it is described as a conjecture of Erdős and Newman.
The lower bound of $\sqrt{n}$ is trivial from Parseval's theorem. Körner [Ko80] constructed, for
all $n\geq 2$, polynomials $P(z)=\sum_{k\leq n} a_kz^k$ with $\lvert a_k\rvert=1$ for
$1\leq k\leq n$ such that, for all $z$ with $\lvert z\rvert=1$,
$$(c_1-o(1))\sqrt{n} \leq \lvert P(z)\rvert \leq (c_2+o(1))\sqrt{n}$$
for some absolute constants $0<c_1\leq c_2$.

The answer is no (contrary to Erdős' initial guess). Kahane [Ka80] constructed 'ultraflat'
polynomials $P(z)=\sum a_kz^k$ with $\lvert a_k\rvert=1$ such that
$$P(z)=(1+o(1))\sqrt{n}$$
uniformly for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$, where the $o(1)$ term $\to 0$ as
$n\to \infty$.

For more details see the paper [BoBo09] of Bombieri and Bourgain and where Kahane's construction
is improved to yield such a polynomial with
$$P(z)=\sqrt{n}+O(n^{\frac{7}{18}}(\log n)^{O(1)})$$
for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$.

See also [228](https://www.erdosproblems.com/228) and
[1150](https://www.erdosproblems.com/1150).
-/
@[category research solved, AMS 30 42, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos230.lean#L40"]
theorem erdos_230 : answer(False) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ a : Fin n → ℂ, (∀ k, ‖a k‖ = 1) → (1 + c) * √n ≤ circleMax a := by
  sorry

/--
Kahane [Ka80] constructed 'ultraflat' polynomials $P_n(z)=\sum_{k \leq n} a_kz^k$ with
$\lvert a_k\rvert=1$ such that $P_n(z)=(1+o(1))\sqrt{n}$ uniformly for all $z\in\mathbb{C}$ with
$\lvert z\rvert=1$.
-/
@[category research solved, AMS 30 42]
theorem erdos_230.variants.ultraflat : ∃ a : (n : ℕ) → Fin n → ℂ, (∀ n k, ‖a n k‖ = 1) ∧
    Tendsto (fun n : ℕ => ⨆ z : Metric.sphere (0 : ℂ) 1,
      |‖∑ k : Fin n, a n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / √n - 1|) atTop (𝓝 0) := by
  sorry

end Erdos230

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
# Erdős Problem 821

*References:*
- [erdosproblems.com/821](https://www.erdosproblems.com/821)
- [BaHa98] Baker, R. C. and Harman, G., Shifted primes without large prime factors. Acta Arith.
  (1998), 331--361.
- [Er35b] Erdős, P., On the normal number of prime factors of $p-1$ and some related problems
  concerning Euler's $\varphi$-function. Quart. J. Math. (1935), 205-213.
- [Er74b] Erdős, P., Remarks on some problems in number theory. Math. Balkanica (1974), 197-202.
- [Li22] J. D. Lichtman, Primes in arithmetic progressions to large moduli and shifted primes
  without large prime factors. arXiv:2211.09641 (2022).
- [LuPo11] Luca, Florian and Pollack, Paul, An arithmetic function arising from {C}armichael's
  conjecture. J. Théor. Nombres Bordeaux (2011), 697--714.
-/

open Nat Filter

namespace Erdos821

/--
Let $g(n)$ count the number of $m$ such that $\phi(m)=n$.
-/
noncomputable def g (n : ℕ) : ℕ :=
  { m : ℕ | totient m = n }.ncard

/--
Is it true that, for every $\epsilon>0$, there exist infinitely many $n$ such that
$g(n) > n^{1-\epsilon}$?
-/
@[category research open, AMS 11]
theorem erdos_821 :
    answer(sorry) ↔ ∀ ε > (0 : ℝ), { n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε) }.Infinite := by
  sorry

/--
Pillai proved that $\limsup g(n)=\infty$.
-/
@[category research solved, AMS 11]
theorem erdos_821.variants.pillai :
    atTop.limsup (fun n : ℕ ↦ (g n : EReal)) = ⊤ := by
  sorry

/--
Erdős [Er35b] proved that there exists some constant $c>0$ such that $g(n) > n^c$ for infinitely
many $n$.
-/
@[category research solved, AMS 11]
theorem erdos_821.variants.erdos :
    ∃ c > (0 : ℝ), { n : ℕ | (n : ℝ) ^ c < (g n : ℝ) }.Infinite := by
  sorry

/--
The best known bound is that there are infinitely many $n$ such that $g(n) > n^{0.71568\cdots}$,
obtained by Lichtman [Li22] as a consequence of proving that there are
$\geq \frac{x}{(\log x)^{O(1)}}$ many primes $p\leq x$ such that all prime factors of $p-1$ are
$\leq x^{0.2843\cdots}$ (which improves a number of previous exponents, most recently Baker and
Harman [BaHa98]).
-/
@[category research solved, AMS 11]
theorem erdos_821.variants.lichtman :
    ∃ c > (0.71568 : ℝ), { n : ℕ | (n : ℝ) ^ c < (g n : ℝ) }.Infinite := by
  sorry

end Erdos821

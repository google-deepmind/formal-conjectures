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
# Erdős Problem 841

*References:*
- [erdosproblems.com/841](https://www.erdosproblems.com/841)
- [ErSe92] Erdős, Paul and Selfridge, J. L., Problems and Solutions: Solutions: 6655. Amer. Math.
  Monthly (1992), 791--794.
- [BPZ24] Bui, Hung M. and Pratt, Kyle and Zaharescu, Alexandru, A problem of
  Erdős-Graham-Granville-Selfridge on integral points on hyperelliptic curves. Math. Proc.
  Cambridge Philos. Soc. (2024), 309--323.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
-/

@[expose] public section

open Filter Real Topology

namespace Erdos841

/-- `t n` is the least `T` such that `{n + 1, …, n + T}` contains a subset whose product with `n`
is a square; `t n = 0` if and only if `n` is itself a square. -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))}

open scoped Classical in
/--
Let $t_n$ be minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose product with $n$ is
a square number (and let $t_n=0$ if $n$ is itself square). Estimate $t_n$.

A problem of Erdős, Graham, and Selfridge. For example, $t_6=6$ since $6\cdot 8\cdot 12=24^2$. It
is trivial that $t_n\geq P(n)$, where $P(n)$ is the largest prime divisor of $n$.

Bui, Pratt, and Zaharescu [BPZ24] proved that the distribution of $t_n$ continues to follow
$P(n)$, in that for any fixed $c\in (0,1]$
$$\lim_{x\to \infty}\frac{\lvert \{ n\leq x : t_n\leq n^c\}\rvert}{x}
  = \lim_{x\to \infty}\frac{\lvert \{ n\leq x : P(n)\leq n^c\}\rvert}{x}.$$
The statement below is that the difference of the two counting functions is $o(x)$.

This was formalized in Lean by Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/Core.lean#L16920"]
theorem erdos_841 (c : ℝ) (hc : c ∈ Set.Ioc 0 1) :
    Tendsto (fun x : ℕ ↦
      ((((Finset.Icc 1 x).filter fun n : ℕ ↦ (t n : ℝ) ≤ (n : ℝ) ^ c).card : ℝ) -
        ((Finset.Icc 1 x).filter fun n : ℕ ↦ (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ c).card) / x)
      atTop (𝓝 0) := by
  sorry

/--
Selfridge proved that $t_n=P(n)$ if $P(n)>\sqrt{2n}+1$.

This was formalized in Lean by Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/LowerBound.lean#L3183"]
theorem erdos_841.variants.selfridge_large_prime (n : ℕ) (hn : 1 < n)
    (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) : t n = n.maxPrimeFac := by
  sorry

/--
Selfridge proved that $t_n \ll n^{1/2}$ if $P(n)\leq\sqrt{2n}+1$.

This was formalized in Lean by Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/Core.lean#L1373"]
theorem erdos_841.variants.selfridge_sqrt :
    ∃ C : ℝ, ∀ n : ℕ, (n.maxPrimeFac : ℝ) ≤ √(2 * n) + 1 → (t n : ℝ) ≤ C * √n := by
  sorry

open scoped Classical in
/--
Bui, Pratt, and Zaharescu [BPZ24] proved that for at least $x^{1-o(1)}$ many $n\leq x$ we have
$$t_n \leq \exp(O(\sqrt{\log n\log\log n})).$$

This was formalized in Lean by Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/Core.lean#L16105"]
theorem erdos_841.variants.many_small_values : ∃ K : ℝ,
    Tendsto (fun x : ℕ ↦
      log (((Finset.Icc 1 x).filter fun n ↦
        (t n : ℝ) ≤ exp (K * √(log n * log (log n)))).card : ℝ) / log x) atTop (𝓝 1) := by
  sorry

/--
Bui, Pratt, and Zaharescu [BPZ24] proved that for all non-square $n$
$$t_n \gg (\log\log n)^{6/5}(\log\log\log n)^{-1/5}.$$

This was formalized in Lean by Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/LowerBound.lean#L3166"]
theorem erdos_841.variants.lower_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ¬ IsSquare n →
      C * (log (log n) ^ ((6 : ℝ) / 5) * log (log (log n)) ^ (-(1 : ℝ) / 5)) ≤ t n := by
  sorry

end Erdos841

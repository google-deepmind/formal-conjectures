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
# The reverse Littlewood–Offord problem at radius one: the odd-$n$ exponential rate

*Reference:* [arxiv/2503.24202](https://arxiv.org/abs/2503.24202)
**Double-jump phase transition for the reverse Littlewood–Offord problem**
by *Lawrence Hollom, Julien Portier, Victor Souza*

*Upper bound:* L. Hollom and G. B. Sorkin, *Reverse Littlewood–Offord problems with parity
conditions*, [arXiv:2510.05044](https://arxiv.org/abs/2510.05044), Theorem 1.3.

*Formal proof:* Kenta Kitamura,
[The reverse Littlewood–Offord problem at radius one in Lean](https://github.com/KitaKen1/reverse-littlewood-offord-lean/tree/40fd4a7f6257c7dba70ea8bf948fb3635cc7600c).

For unit vectors $v_1, \dots, v_n \in \mathbb{R}^2$ and independent uniform signs
$\varepsilon_i \in \{-1, 1\}$, let $F_{2,1}(n)$ be the infimum of
$\mathbb{P}(\lVert \varepsilon_1 v_1 + \dots + \varepsilon_n v_n \rVert_2 \le 1)$.
Question 7.1 of the source asks how fast $F_{2,1}(n)$ decays for odd $n$; the source records
that the decay is exponential and leaves open whether $F_{2,1}(n)^{1/n}$ converges, and to what.
-/

@[expose] public section

open Filter Topology

namespace Arxiv.«2503.24202»

/--
**Open problem after Question 7.1 (Hollom-Portier-Souza, 2025).** Does
$\lim_{n \to \infty,\ n \text{ odd}} F_{2,1}(n)^{1/n}$ exist, and if so, what is its value?

The limit exists and equals $1/\sqrt{2}$. The upper bound $F_{2,1}(n) \le 2^{-\lfloor n/2 \rfloor}$
is Theorem 1.3 of arXiv:2510.05044; the matching lower bound and the limit are proved in the
formal proof linked below. Planar vectors are complex numbers, a sign vector is
`ε : Fin n → Bool` with `true` for $+1$, and $n = 2k + 1$.
-/
@[category research solved, AMS 5 60,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/reverse-littlewood-offord-lean/blob/40fd4a7f6257c7dba70ea8bf948fb3635cc7600c/lean/ReverseLittlewoodOffordFC.lean#L31-L39"]
theorem reverse_littlewood_offord_rate :
    Tendsto
      (fun k : ℕ =>
        (⨅ v : {v : Fin (2 * k + 1) → ℂ // ∀ i, ‖v i‖ = 1},
          ((Finset.univ.filter fun ε : Fin (2 * k + 1) → Bool =>
              ‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1).card : ℝ) / 2 ^ (2 * k + 1))
          ^ (1 / (2 * k + 1 : ℝ)))
      atTop (𝓝 (answer(1 / Real.sqrt 2) : ℝ)) := by
  sorry

end Arxiv.«2503.24202»

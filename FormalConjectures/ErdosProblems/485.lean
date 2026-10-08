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
# Erdős Problem 485

*References:*
- [erdosproblems.com/485](https://www.erdosproblems.com/485)
- [Re47] Rényi, A., *On the minimal number of terms of the square of a polynomial*. Hungarica Acta
  Math. (1947), 30-34.
- [Er49b] Erdős, P., *On the number of terms of the square of a polynomial*. Nieuw Arch. Wiskunde
  (2) (1949), 63-65.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
- [Sc87] Schinzel, A., *On the number of terms of a power of a polynomial*. Acta Arith. (1987),
  55-70.
- [ScZa09] Schinzel, Andrzej and Zannier, Umberto, *On the number of terms of a power of a
  polynomial*. Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. (2009), 95-98.
-/

@[expose] public section

open Filter Polynomial

namespace Erdos485

/-- The minimum number of terms of the square of a rational polynomial with exactly `k` nonzero
terms, where the number of terms of `P` is `P.support.card`. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {m | ∃ P : ℚ[X], P.support.card = k ∧ (P ^ 2).support.card = m}

/--
Let $f(k)$ be the minimum number of terms in $P(x)^2$, where $P \in \mathbb{Q}[x]$ ranges over all
polynomials with exactly $k$ non-zero terms. Is it true that $f(k) \to \infty$ as $k \to \infty$?

A conjecture of Erdős and Rényi (this is Problem 4.4 in [Ha74], attributed to Erdős); the
function was first investigated by Rényi and Rédei [Re47], and Erdős [Er49b] proved that
$f(k) < k^{1-c}$ for some $c > 0$. The answer is yes: Schinzel [Sc87] proved
$f(k) > \log \log k / \log 2$, and Schinzel and Zannier [ScZa09] improved this to
$f(k) \gg \log k$.
-/
@[category research solved, AMS 11 12, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos485.lean#L39"]
theorem erdos_485 : answer(True) ↔ Tendsto f atTop atTop := by
  sorry

end Erdos485

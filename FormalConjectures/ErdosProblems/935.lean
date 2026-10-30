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
public import FormalConjectures.ErdosProblems.«367»

/-!
# Erdős Problem 935

*References:*
- [erdosproblems.com/935](https://www.erdosproblems.com/935)
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
  [PDF](https://www.renyi.hu/~p_erdos/1976-39.pdf)
- [Fe26] Feng, T. et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. [arXiv:2601.22401](https://arxiv.org/abs/2601.22401) (2026).

The powerful part $Q_2(m)$ of $m$ is `Erdos367.B 2 m`, the product of $p^a$ over the primes $p$
with $p^a \parallel m$ and $a \geq 2$. The second question is essentially the same as
[erdosproblems.com/367](https://www.erdosproblems.com/367).
-/

@[expose] public section

open Filter

namespace Erdos935

/--
For any integer $n=\prod p^{k_p}$ let $Q_2(n)$ be the powerful part of $n$, so that
$$Q_2(n) = \prod_{\substack{p\\ k_p\geq 2}}p^{k_p}.$$
Is it true that, for every $\epsilon>0$ and $\ell\geq 1$, if $n$ is sufficiently large then
$$Q_2(n(n+1)\cdots(n+\ell))<n^{2+\epsilon}?$$

A problem of Erdős [Er76d, p. 32], who writes that if this is true then it seems very difficult to
prove. This is the first part.
-/
@[category research open, question, AMS 11]
theorem erdos_935.parts.i :
    ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ᶠ n : ℕ in atTop,
      ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) < (n : ℝ) ^ (2 + ε) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For any integer $n=\prod p^{k_p}$ let $Q_2(n)$ be the powerful part of $n$, so that
$$Q_2(n) = \prod_{\substack{p\\ k_p\geq 2}}p^{k_p}.$$
If $\ell\geq 2$ then is
$$\limsup_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^2}$$
infinite?

This is the second part. We write "infinite" as: for every $C$, $C n^2 < Q_2(\cdots)$ for infinitely
many $n$. The answer is yes, by the Pell equation construction of `erdos_935.variants.ell_two`
(the case $\ell = 2$); for larger $\ell$ the product for $\ell = 2$ divides the product for $\ell$,
and $Q_2$ does not decrease under divisibility.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/veljjanoski/formal-conjectures-proofs/blob/03e17cd05ef4d72abf00c889294efcfe9feb0d5f/FcProofs/Erdos935.lean#L104"]
theorem erdos_935.parts.ii :
    ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  sorry

/--
For any integer $n=\prod p^{k_p}$ let $Q_2(n)$ be the powerful part of $n$, so that
$$Q_2(n) = \prod_{\substack{p\\ k_p\geq 2}}p^{k_p}.$$
If $\ell\geq 2$ then is
$$\lim_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^{\ell+1}}=0?$$

This is the third part. The restriction $\ell \geq 2$ is needed: for $\ell = 1$ the Pell solutions of
`erdos_935.variants.mahler` give $Q_2(n(n+1)) = n(n+1)$ infinitely often.
-/
@[category research open, question, AMS 11]
theorem erdos_935.parts.iii :
    ∀ ℓ : ℕ, 2 ≤ ℓ → Tendsto
      (fun n : ℕ ↦ ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) / (n : ℝ) ^ (ℓ + 1))
      atTop (nhds 0) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
A result of Mahler implies, for every $\ell\geq 1$,
$$\limsup_{n\to \infty}\frac{Q_2(n(n+1)\cdots(n+\ell))}{n^2}\geq 1.$$

Erdős [Er76d, pp. 31-32] derives this from the infinitely many solutions of $x^2-8y^2=1$, which
give consecutive powerful numbers. We write $\limsup \geq 1$ as: for every $\varepsilon > 0$,
$(1-\varepsilon) n^2 < Q_2(\cdots)$ for infinitely many $n$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/veljjanoski/formal-conjectures-proofs/blob/03e17cd05ef4d72abf00c889294efcfe9feb0d5f/FcProofs/Erdos935.lean#L156"]
theorem erdos_935.variants.mahler :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      (1 - ε) * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
The construction of van Doorn for [367] (also given by Aletheia [Fe26, §4.2]) proves the second
part in the affirmative: a construction via solutions to the Pell equation $x^2-8y^2=1$ implies
$$\limsup_{n\to \infty}\frac{Q_2(n(n+1)(n+2))}{n^2}=\infty.$$

This is the case $\ell = 2$, stated as in `erdos_935.parts.ii`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/veljjanoski/formal-conjectures-proofs/blob/03e17cd05ef4d72abf00c889294efcfe9feb0d5f/FcProofs/Erdos935.lean#L150"]
theorem erdos_935.variants.ell_two :
    ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + 2), m) : ℕ) : ℝ) := by
  sorry

end Erdos935

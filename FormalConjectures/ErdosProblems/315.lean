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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 315

*References:*
- [erdosproblems.com/315](https://www.erdosproblems.com/315)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ka25] Y. Kamio, *Asymptotic analysis of infinite decompositions of a unit fraction into unit
  fractions*. arXiv:2503.02317 (2025).
- [LiTa25] Z. Li and Q. Tang, *On a conjecture of Erdős and Graham about the Sylvester's
  sequence*. arXiv:2503.12277 (2025).
-/

open Filter

namespace Erdos315

/-- The sequence $u_1=1$, $u_{n+1}=u_n(u_n+1)$, indexed here so that `u i` is $u_{i+1}$:
`u 0 = 1`, `u 1 = 2`, `u 2 = 6`, `u 3 = 42`, … (so `u i + 1` is Sylvester's sequence
$2, 3, 7, 43, \ldots$). -/
def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

/-- The Vardi constant $c_0=\lim u_n^{1/2^n}=1.264085\cdots$. With the `0`-indexing of `u`, the
$n$-th term $u_n^{1/2^n}$ of the defining sequence is `(u i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))` at
`i = n - 1`. -/
noncomputable def c₀ : ℝ := limUnder atTop fun i => (u i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))

/--
Let $u_1=1$ and $u_{n+1}=u_n(u_n+1)$, so that $\sum_{k\geq 1}\frac{1}{u_k+1}$ and
$u_k=\lfloor c_0^{2^k}+1\rfloor$ for $k\geq 1$, where
\[c_0=\lim u_n^{1/2^n}=1.264085\cdots.\]
Let $a_1<a_2<\cdots $ be any other sequence with $\sum \frac{1}{a_k}=1$. Is it true that
\[\liminf a_n^{1/2^n}<c_0=1.264085\cdots?\]

This is true, and was proved independently by Kamio [Ka25] and Li and Tang [LiTa25].

An earlier interpretation of this question on this site defined $u_1=2$ and
$u_{n+1}=u_n^2-u_n+1$ (Sylvester's sequence), which is the same sequence shifted by $1$; we use
the phrasing above as more faithful to [ErGr80]. The constant $c_0$ is called the Vardi constant.

Formalisation note: `a i` and `u i` denote $a_{i+1}$ and $u_{i+1}$, so the exponent $1/2^n$
becomes `(1 / 2) ^ (i + 1)`, and "any other sequence" is expressed as `∃ i, a i ≠ u i + 1`, the
sequence $(u_k+1)_{k\geq 1}$ being the given decomposition with $\sum_{k\geq 1}\frac{1}{u_k+1}=1$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos315.lean"]
theorem erdos_315 : answer(True) ↔
    ∀ a : ℕ → ℕ, (∀ i, 0 < a i) → StrictMono a → (∃ i, a i ≠ u i + 1) →
      ∑' i, (1 : ℝ) / a i = 1 →
      atTop.liminf (fun i => (a i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))) < c₀ := by
  sorry

end Erdos315

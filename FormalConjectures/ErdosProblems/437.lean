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
# Erdős Problem 437

*References:*
- [erdosproblems.com/437](https://www.erdosproblems.com/437)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [BPZ24] Bui, Hung M. and Pratt, Kyle and Zaharescu, Alexandru, _A problem of
  Erdős-Graham-Granville-Selfridge on integral points on hyperelliptic curves_. Math. Proc.
  Cambridge Philos. Soc. (2024), 309--323.
- [Ta24] Tao, Terence, _A result of Bui–Pratt–Zaharescu, and Erdős problem #437_. Blog post
  (2024).
-/

@[expose] public section

open Filter Real

namespace Erdos437

/-- The number of partial products $a_1, a_1a_2, \ldots, a_1\cdots a_k$ of a finite sequence
`a = [a₁, …, a_k]` which are squares. -/
def squarePartialProducts (a : List ℕ) : ℕ :=
  ((Finset.range a.length).filter fun i ↦ IsSquare (a.take (i + 1)).prod).card

/-- `L x` is the maximal number of square partial products of a sequence
$1\leq a_1<\cdots<a_k\leq x$. -/
noncomputable def L (x : ℕ) : ℕ :=
  sSup {m | ∃ a : List ℕ, a.Pairwise (· < ·) ∧ (∀ n ∈ a, n ∈ Finset.Icc 1 x) ∧
    squarePartialProducts a = m}

/--
Let $1\leq a_1<\cdots<a_k\leq x$. How many of the partial products
$a_1,a_1a_2,\ldots,a_1\cdots a_k$ can be squares? Is it true that, for any $\epsilon>0$, there can
be more than $x^{1-\epsilon}$ squares?

The answer is yes, which follows from work of Bui, Pratt, and Zaharescu [BPZ24], as noted by
Tao [Ta24].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos437.lean#L746"]
theorem erdos_437 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (1 - ε) < L x := by
  sorry

/--
Erdős and Graham write it is 'trivial' that there are $o(x)$ many such squares, although this is
not quite trivial, using Siegel's theorem.
-/
@[category research solved, AMS 11]
theorem erdos_437.variants.little_o :
    (fun x : ℕ ↦ (L x : ℝ)) =o[atTop] fun x : ℕ ↦ (x : ℝ) := by
  sorry

/--
Tao [Ta24] shows that, if $u(x)=(\log x\log\log x)^{1/2}$, then
$$x\exp(-(2^{1/2}+o(1))u(x)) \leq L(x) \leq x\exp(-(2^{-1/2}+o(1))u(x)).$$
-/
@[category research solved, AMS 11]
theorem erdos_437.variants.tao :
    ∃ o₁ o₂ : ℕ → ℝ, Tendsto o₁ atTop (nhds 0) ∧ Tendsto o₂ atTop (nhds 0) ∧
      ∀ᶠ x : ℕ in atTop,
        x * exp (-(√2 + o₁ x) * √(log x * log (log x))) ≤ L x ∧
        L x ≤ x * exp (-((√2)⁻¹ + o₂ x) * √(log x * log (log x))) := by
  sorry

end Erdos437

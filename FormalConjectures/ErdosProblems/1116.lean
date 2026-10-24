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
# Erdős Problem 1116

*References:*
- [erdosproblems.com/1116](https://www.erdosproblems.com/1116)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. Proceedings of
  the Symposium on Complex Analysis (Canterbury, 1973), London Math. Soc. Lecture Note Ser. 12
  (1974), 155--180.
- [To76] Toppila, Sakari, *On the counting function for the $a$-values of a meromorphic
  function*. Ann. Acad. Sci. Fenn. Ser. A I Math. 2 (1976), 565--572.
  [PDF](https://www.acadsci.fi/mathematica/Vol02/vol02pp565-572.pdf)
- [Go78] Gol'dberg, A. A., *Counting functions of sequences of $a$-points for entire
  functions*. Sibirsk. Mat. Zh. 19 (1978), 28--36, 236.
- [HaLi18] Hayman, W. K. and Lingham, E. F., *Research problems in function theory*.
  [arXiv:1809.07200](https://arxiv.org/abs/1809.07200) (2018).
-/

@[expose] public section

namespace Erdos1116

/--
$n(r,a)$ for $f$: the number of roots of $f(z)=a$ in the open disc $\lvert z\rvert<r$, counted
with multiplicity, as on erdosproblems.com. [To76, p. 565] and [HaLi18, Chapter 1, Notation]
count roots in the closed disc $\lvert z\rvert\le r$; this does not change the $\limsup$ below,
since the open-disc count at $r$ equals the closed-disc count at some slightly smaller radius.

The count is the sum, over the disc, of the positive part of the divisor of $f-a$. For an entire
$f$ the divisor has finite support, so `∑ᶠ` is the ordinary finite sum. For $f \equiv a$ the
divisor is $0$.
-/
noncomputable def aPointCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  ∑ᶠ z : ℂ,
    Int.toNat (MeromorphicOn.divisor (fun w ↦ f w - a) (Metric.ball (0 : ℂ) r) z)

/--
Division-free form of $\limsup_{r\to\infty} n(r,a)/n(r,b)=\infty$. For every $M$ and $R$ there
is $r>R$ with $n(r,b)>0$ and $n(r,a)>M\,n(r,b)$. In particular, $f$ takes the value $b$, so
the ratio is never $x/0$.
-/
def UnboundedCountRatio (f : ℂ → ℂ) (a b : ℂ) : Prop :=
  ∀ M : ℕ, ∀ R : ℝ, ∃ r : ℝ, R < r ∧
    0 < aPointCount f r b ∧ M * aPointCount f r b < aPointCount f r a

/--
For a meromorphic function $f$ let $n(r,a)$ count the number of roots of $f(z)=a$ in the disc
$\lvert z\rvert <r$. Does there exist a meromorphic (or entire) $f$ such that for every
$a\neq b$
$$\limsup_{r\to \infty}\frac{n(r,a)}{n(r,b)}=\infty?$$

This is Problem 1.25 in [Ha74], where it is attributed to Erdős. Gol'dberg [Go78] and Toppila
[To76, Theorem 3] constructed such entire functions. We state this case, for finite
$a\neq b$, using `UnboundedCountRatio`.
-/
@[category research solved, question, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1116.lean#L4968"]
theorem erdos_1116 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b → UnboundedCountRatio f a b := by
  sorry

end Erdos1116

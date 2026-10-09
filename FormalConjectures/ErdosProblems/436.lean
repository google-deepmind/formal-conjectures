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
# Erdős Problem 436

*References:*
- [erdosproblems.com/436](https://www.erdosproblems.com/436)
- [BLL64] Brillhart, John and Lehmer, D. H. and Lehmer, Emma, *Bounds for pairs of consecutive
  seventh and higher power residues*. Math. Comp. (1964), 397--407.
- [BiMi63] Bierstedt, R. G. and Mills, W. H., *On the bound for a pair of consecutive quartic
  residues of a prime*. Proc. Amer. Math. Soc. (1963), 628--632.
- [Du65] Dunton, M., *Bounds for pairs of cubic residues*. Proc. Amer. Math. Soc. (1965),
  330--332.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Gr64g] Graham, R. L., *On quadruples of consecutive $k$th power residues*. Proc. Amer. Math.
  Soc. (1964), 196--197.
- [Hi91] Hildebrand, Adolf, *On consecutive $k$th power residues. II*. Michigan Math. J. (1991),
  241-253.
- [LLM63] Lehmer, D. H. and Lehmer, Emma and Mills, W. H., *Pairs of consecutive power residues*.
  Canadian J. Math. (1963), 172--177.
- [LLMS62] Lehmer, D. H. and Lehmer, E. and Mills, W. H. and Selfridge, J. L., *Machine proof of a
  theorem on cubic residues*. Math. Comp. (1962), 407--415.
- [LeLe62] Lehmer, D. H. and Lehmer, Emma, *On runs of residues*. Proc. Amer. Math. Soc. (1962),
  102-106.
-/

@[expose] public section

open Filter

namespace Erdos436

/-- `IsPowerResidue k p n` means that $n$ is a $k$th power residue modulo $p$ (intended for a prime
$p$): $p \nmid n$ and $x^k \equiv n \pmod p$ has a solution $x$. -/
def IsPowerResidue (k p n : ℕ) : Prop :=
  (n : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = (n : ZMod p)

/-- `HasRunUpTo k m p R` means that the $m$ integers $r, r+1, \ldots, r+m-1$ are all $k$th power
residues modulo $p$ for some integer $r$ with $1 \leq r \leq R$.

For a prime $p$, this says that $r(k, m, p)$ exists and $r(k, m, p) \leq R$, where $r(k, m, p)$ is
the least such $r \geq 1$. -/
def HasRunUpTo (k m p R : ℕ) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ ∀ i < m, IsPowerResidue k p (r + i)

/-- `LambdaFinite k m` states that $\Lambda(k, m) < \infty$, where
$$\Lambda(k, m) = \limsup_{p \to \infty} r(k, m, p)$$
and $r(k, m, p)$ is the least $r \geq 1$ such that $r, r+1, \ldots, r+m-1$ are all $k$th power
residues modulo $p$.

It says that there is a bound $R$ such that, for all sufficiently large primes $p$, some run of
$m$ consecutive $k$th power residues starts at an $r \leq R$. The statement $\Lambda(k, m) = \infty$
is the negation. -/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ R : ℕ, ∀ᶠ p : ℕ in atTop, p.Prime → HasRunUpTo k m p R

/-- `LambdaEq k m L` states that $\Lambda(k, m) = L$ for a natural number $L$.

It says that, for all sufficiently large primes $p$, some run of $m$ consecutive $k$th power
residues starts at an $r \leq L$, and that for every $R < L$ infinitely many primes $p$ have no
such run with $r \leq R$. As $r(k, m, p)$ is an integer, this is exactly
$\limsup_{p \to \infty} r(k, m, p) = L$. -/
def LambdaEq (k m L : ℕ) : Prop :=
  (∀ᶠ p : ℕ in atTop, p.Prime → HasRunUpTo k m p L) ∧
    ∀ R < L, ∃ᶠ p : ℕ in atTop, p.Prime ∧ ¬ HasRunUpTo k m p R

/-- The integer $p$ itself is not a $k$th power residue modulo $p$. -/
@[category test, AMS 11]
theorem not_isPowerResidue_self (k p : ℕ) : ¬ IsPowerResidue k p p := by
  rintro ⟨h, -⟩
  exact h (ZMod.natCast_self p)

/-- The quadratic residues modulo $13$ are $1, 3, 4, 9, 10, 12$, so the first pair of consecutive
quadratic residues modulo $13$ is $3, 4$, and $r(2, 2, 13) = 3$. -/
@[category test, AMS 11]
theorem hasRunUpTo_two_two_thirteen : HasRunUpTo 2 2 13 3 ∧ ¬ HasRunUpTo 2 2 13 2 := by
  have h2 : ¬ IsPowerResidue 2 13 2 := by
    unfold IsPowerResidue
    decide
  refine ⟨⟨3, by norm_num, le_rfl, fun i hi => ?_⟩, ?_⟩
  · interval_cases i <;> (unfold IsPowerResidue; decide)
  · rintro ⟨r, hr1, hr2, h⟩
    interval_cases r
    · exact h2 (h 1 (by norm_num))
    · exact h2 (h 0 (by norm_num))

/-- If $\Lambda(k, m) = L$, then $\Lambda(k, m)$ is finite. -/
@[category API, AMS 11]
theorem LambdaEq.lambdaFinite {k m L : ℕ} (h : LambdaEq k m L) : LambdaFinite k m :=
  ⟨L, h.1⟩

/--
If $p$ is a prime and $k,m\geq 2$ then let $r(k,m,p)$ be the minimal $r$ such that
$r,r+1,\ldots,r+m-1$ are all $k$th power residues modulo $p$. Let
$$\Lambda(k,m)=\limsup_{p\to \infty} r(k,m,p).$$
Is it true that $\Lambda(k,2)$ is finite for all $k$?

Asked by Lehmer and Lehmer [LeLe62]; see also [ErGr80]. Hildebrand [Hi91] resolved the first
question, proving that $\Lambda(k,2)$ is finite for all $k$: in other words, for any $k\geq 2$, if
$p$ is sufficiently large then there exists a pair of consecutive $k$th power residues modulo $p$
in $[1,O_k(1)]$.

The source also asks how large $\Lambda(k,2)$ and $\Lambda(k,3)$ are as functions of $k$. This part
is not formalised.
-/
@[category research solved, AMS 11]
theorem erdos_436.parts.i : answer(True) ↔ ∀ k : ℕ, 2 ≤ k → LambdaFinite k 2 := by
  sorry

/--
With $\Lambda(k,m)$ as in `Erdos436.erdos_436.parts.i`, is $\Lambda(k,3)$ finite for all odd $k$?

Here $k \geq 2$, so the odd $k$ are $3, 5, 7, \ldots$. Lehmer, Lehmer, Mills, and Selfridge
[LLMS62] proved that $\Lambda(3,3)=23532$, so the property holds for $k=3$. The question is open
for odd $k \geq 5$. For even $k$, $\Lambda(k,3)=\infty$ by
`Erdos436.erdos_436.variants.even_three`.
-/
@[category research open, AMS 11]
theorem erdos_436.parts.ii : answer(sorry) ↔
    ∀ k : ℕ, 2 ≤ k → Odd k → LambdaFinite k 3 := by
  sorry

/--
Lehmer and Lehmer proved that $\Lambda(k,3)=\infty$ for all even $k$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.even_three :
    ∀ k : ℕ, 2 ≤ k → Even k → ¬ LambdaFinite k 3 := by
  sorry

/--
Graham [Gr64g] proved that $\Lambda(k,l)=\infty$ for all $k\geq 2$ and $l\geq 4$. Lehmer and
Lehmer [LeLe62] proved $\Lambda(k,4)=\infty$ for all $k\leq 1048909$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.four_le :
    ∀ k l : ℕ, 2 ≤ k → 4 ≤ l → ¬ LambdaFinite k l := by
  sorry

/--
Lehmer and Lehmer [LeLe62] note that for example $\Lambda(2,2)=9$ - indeed, $9$ is always a
quadratic residue, and if $10$ isn't then either $2$ or $5$ is, and hence at least one of $1,2$ or
$4,5$ or $9,10$ is a consecutive pair of quadratic residues (and similarly there are infinitely
many $p$ for which there are no consecutive quadratic residues below $9,10$).
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_two_two : LambdaEq 2 2 9 := by
  sorry

/--
A similar argument of Dunton [Du65] proves $\Lambda(3,2)=77$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_three_two : LambdaEq 3 2 77 := by
  sorry

/--
Bierstedt and Mills [BiMi63] proved $\Lambda(4,2)=1224$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_four_two : LambdaEq 4 2 1224 := by
  sorry

/--
Lehmer, Lehmer, and Mills [LLM63] proved $\Lambda(5,2)=7888$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_five_two : LambdaEq 5 2 7888 := by
  sorry

/--
Lehmer, Lehmer, and Mills [LLM63] proved $\Lambda(6,2)=202124$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_six_two : LambdaEq 6 2 202124 := by
  sorry

/--
Brillhart, Lehmer, and Lehmer [BLL64] proved $\Lambda(7,2)=1649375$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_seven_two : LambdaEq 7 2 1649375 := by
  sorry

/--
Lehmer, Lehmer, Mills, and Selfridge [LLMS62] proved that $\Lambda(3,3)=23532$.
-/
@[category research solved, AMS 11]
theorem erdos_436.variants.lambda_three_three : LambdaEq 3 3 23532 := by
  sorry

end Erdos436

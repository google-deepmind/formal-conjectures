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
# Erdős Problem 478

*Reference:* [erdosproblems.com/478](https://www.erdosproblems.com/478)

Let $p$ be a prime and $A_p = \{ k! \bmod p : 1 \leq k < p \}$.
Is it true that $|A_p| \sim (1 - 1/e) \cdot p$?

The best known lower bound is $|A_p| \geq (\sqrt{2} - o(1)) p^{1/2}$
due to Grebennikov, Sagdeev, Semchankau, and Vasilevskii [GSSV24].
Wilson's theorem gives the upper bound $|A_p| \leq p - 2$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[GSSV24] Grebennikov, A., Sagdeev, A., Semchankau, A., and Vasilevskii, A.,
*On the sequence n! mod p*. Revista Matemática Iberoamericana (2024), 637–648.

[HaSu02] Hardy, G. E. and Subbarao, M. V., *A modified problem of Pillai and some
related questions*. Amer. Math. Monthly (2002), 554–559.

[KlMu17] Klurman, O. and Munsch, M., *Distribution of factorials modulo p*.
J. Théor. Nombres Bordeaux (2017), 169–177.
-/

open Filter

open scoped Topology Real

namespace Erdos478

/-- The set of distinct factorial residues modulo $p$:
    $A_p = \{ k! \bmod p : 1 \leq k < p \}$. -/
def factorialResidues (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).image (fun k => Nat.factorial k % p)

/--
Erdős Problem 478 [ErGr80, p.96]:

Let $p$ be a prime and $A_p = \{ k! \bmod p : 1 \leq k < p \}$.
Is it true that $|A_p| \sim (1 - 1/e) \cdot p$?

Formally: the ratio $|A_p| / ((1 - e^{-1}) \cdot p)$ tends to $1$ as $p \to \infty$
through the primes.
-/
@[category research open, AMS 11]
theorem erdos_478 : answer(sorry) ↔
    Tendsto
      (fun p : ℕ =>
        (factorialResidues p).card / ((1 - Real.exp (-1)) * (p : ℝ)))
      (atTop ⊓ Filter.principal {p | Nat.Prime p})
      (nhds 1) := by
  sorry

/--
Hardy–Subbarao conjecture [HaSu02]: only finitely many primes $p$ satisfy
$|A_p| = p - 2$, and perhaps only $p = 5$. Any such prime must satisfy
$p \equiv 1 \pmod{4}$.
-/
@[category research open, AMS 11]
theorem erdos_478_variant_hardy_subbarao : answer(sorry) ↔
    Set.Finite {p : ℕ | Nat.Prime p ∧ (factorialResidues p).card = p - 2} := by
  sorry

end Erdos478

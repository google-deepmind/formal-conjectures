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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 337

*Reference:* [erdosproblems.com/337](https://www.erdosproblems.com/337)

Is it true that for an additive basis $A$ of density $o(N)$, the ratio
$|(A+A) \cap \{1,\ldots,N\}| / |A \cap \{1,\ldots,N\}|$ tends to infinity?
The answer is no, as shown by Turjányi.

Ruzsa and Turjányi [RT85] generalised this negative answer to the $h$-fold sumset $hA$
for any $h \geq 2$. They also proved the positive result that
$|(A+A+A) \cap \{1,\ldots,3N\}| / |A \cap \{1,\ldots,N\}| \to \infty$
for any additive basis $A$ of density $o(N)$, and conjectured that the same holds with
$(A+A) \cap \{1,\ldots,2N\}$ in the numerator.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[ErGr80b] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory II*. (1980).

[Tu84] Turjányi, S., *A note on basis sequences*. Topics in Classical Number Theory, Vol. I, II
(Budapest, 1981), Colloq. Math. Soc. János Bolyai **34** (1984), 1571-1576.

[RT85] Ruzsa, I.Z. and Turjányi, S., *A note on additive bases of integers*. Publ. Math.
Debrecen **32** (1985), 101-104.
-/

open Filter Set

open scoped Topology BigOperators Pointwise

namespace Erdos337

/-- The set of all sums of exactly $k$ elements from $A$ (with repetition). -/
def exactSumset (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- $A \subseteq \mathbb{N}$ is an additive basis of order $r$ if every sufficiently large
natural number is the sum of at most $r$ elements from $A$.

Note: This uses the "at most $r$ summands" convention, which differs from the library's
`Set.IsAsymptoticAddBasisOfOrder` (which requires exactly $n$ summands). The two coincide
when $0 \in A$. -/
def IsAdditiveBasis (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ r, n ∈ exactSumset A k

/--
Erdős Problem 337 [ErGr80] [ErGr80b]:

Let $A \subseteq \mathbb{N}$ be an additive basis (of any finite order) such that
$|A \cap \{1, \ldots, N\}| = o(N)$. Is it true that
$$\lim_{N \to \infty} \frac{|(A+A) \cap \{1, \ldots, N\}|}{|A \cap \{1, \ldots, N\}|} = \infty?$$

The answer is no. A counterexample was provided by Turjányi [Tu84].
This was generalised (replacing $A+A$ by the $h$-fold sumset $hA$ for any
$h \geq 2$) by Ruzsa and Turjányi [RT85].
-/
@[category research solved, AMS 11]
theorem erdos_337 : answer(False) ↔
    ∀ (A : Set ℕ),
      (∃ r : ℕ, IsAdditiveBasis A r) →
      A.HasDensity 0 →
      Tendsto (fun N => (A + A).partialDensity N / A.partialDensity N) atTop atTop := by
  sorry

/--
Ruzsa–Turjányi generalization [RT85]: The negative answer to Erdős Problem 337 extends
to the $h$-fold sumset $hA$ for any $h \geq 2$. That is, for any $h \geq 2$, there exists
an additive basis $A$ of density $o(N)$ such that
$|hA \cap \{1,\ldots,N\}| / |A \cap \{1,\ldots,N\}|$ does not tend to infinity.
-/
@[category research solved, AMS 11]
theorem erdos_337_hfold (h : ℕ) (hh : 2 ≤ h) :
    ¬ ∀ (A : Set ℕ),
      (∃ r : ℕ, IsAdditiveBasis A r) →
      A.HasDensity 0 →
      Tendsto (fun N => (exactSumset A h).partialDensity N / A.partialDensity N)
        atTop atTop := by
  sorry

/--
Ruzsa–Turjányi positive result [RT85]: For any additive basis $A$ of density $o(N)$,
the ratio $|(A+A+A) \cap \{1,\ldots,3N\}| / |A \cap \{1,\ldots,N\}|$ tends to infinity.
-/
@[category research solved, AMS 11]
theorem erdos_337_triple_sumset :
    ∀ (A : Set ℕ),
      (∃ r : ℕ, IsAdditiveBasis A r) →
      A.HasDensity 0 →
      Tendsto (fun N =>
        ((Set.interIio (A + A + A) (3 * N)).ncard : ℝ) /
        ((Set.interIio A N).ncard : ℝ)) atTop atTop := by
  sorry

end Erdos337

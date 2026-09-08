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

import FormalConjecturesUtil

/-!
# Kaplansky's problem on the values of the $u$-invariant

The $u$-invariant $u(F)$ of a field $F$ is the largest dimension of an anisotropic quadratic form
over $F$, or $\infty$ if there is no largest one; that is, $u(F) = n$ exactly when
`IsGreatest (QuadraticForm.anisotropicDims F) n`. Following [Kaplansky1953] and
[MerkurjevParimala2025, §5.1], all fields are of characteristic not $2$.

Kaplansky introduced the invariant (his $C(F)$) in [Kaplansky1953, p. 201], proved that $u(F) \ne 3$
(his Theorem 2), observed that every power of $2$ occurs (his Theorem 3 gives
$u(F((t))) = 2u(F)$), and conjectured that $u(F)$ is a power of $2$ whenever it is finite
[Kaplansky1953, p. 202]. It is classical that $u(F) \notin \{3, 5, 7\}$
[Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. Merkurjev disproved Kaplansky's
conjecture with a field of $u$-invariant $6$ [Merkurjev1989] and then showed that every positive
even integer is a $u$-invariant [Merkurjev1991]. Izhboldin constructed a field of $u$-invariant
$9$ [Izhboldin2001], and Vishik fields of $u$-invariant $2^r + 1$ for every $r \ge 3$
[Vishik2009]. A 2026 preprint of Karpenko constructs fields of $u$-invariant $n$ for every $n$
that is neither of the form $2^r - 1$ nor of the form $2^r - 3$ [Karpenko2026]; as of September
2026 it is not yet peer-reviewed.

The problem (`u_invariant_values`) is to determine which integers are $u$-invariants of fields.
The survey [MerkurjevParimala2025, §5.1] records the expectation that every odd integer $\ge 9$
is a $u$-invariant (`u_invariant_values.variants.odd`). Given the results above, the problem is
open exactly for the integers $2^r - 1$ and $2^r - 3$ with $r \ge 4$, the smallest of which are
$13$ and $15$.

*References:*
- [Kaplansky1953] I. Kaplansky, *Quadratic forms*, J. Math. Soc. Japan 5 (1953), 200–207,
  [doi:10.2969/jmsj/00520200](https://doi.org/10.2969/jmsj/00520200).
- [Lam2005] T. Y. Lam, *Introduction to quadratic forms over fields*, Grad. Stud. Math. 67,
  Amer. Math. Soc., 2005, [doi:10.1090/gsm/067](https://doi.org/10.1090/gsm/067).
- [EKM2008] R. Elman, N. Karpenko, A. Merkurjev, *The algebraic and geometric theory of quadratic
  forms*, Amer. Math. Soc. Colloq. Publ. 56, Amer. Math. Soc., 2008,
  [doi:10.1090/coll/056](https://doi.org/10.1090/coll/056).
- [Merkurjev1989] A. S. Merkurjev, *Kaplansky's conjecture in the theory of quadratic forms*
  (Russian), Zap. Nauchn. Sem. LOMI 175 (1989), 75–89; English transl. J. Soviet Math. 57
  (1991), no. 6, 3489–3497, [doi:10.1007/BF01100118](https://doi.org/10.1007/BF01100118).
- [Merkurjev1991] A. S. Merkurjev, *Simple algebras and quadratic forms* (Russian), Izv. Akad.
  Nauk SSSR Ser. Mat. 55 (1991), no. 1, 218–224; English transl. Math. USSR-Izv. 38 (1992),
  no. 1, 215–221,
  [doi:10.1070/IM1992v038n01ABEH002195](https://doi.org/10.1070/IM1992v038n01ABEH002195).
- [Izhboldin2001] O. T. Izhboldin, *Fields of $u$-invariant $9$*, Ann. of Math. (2) 154 (2001),
  no. 3, 529–587, [doi:10.2307/3062141](https://doi.org/10.2307/3062141).
- [Vishik2009] A. Vishik, *Fields of $u$-invariant $2^r + 1$*, pp. 661–685 in Algebra,
  arithmetic, and geometry: in honor of Yu. I. Manin, Vol. II, Progr. Math. 270, Birkhäuser,
  2009, [doi:10.1007/978-0-8176-4747-6_22](https://doi.org/10.1007/978-0-8176-4747-6_22).
- [Karpenko2026] N. A. Karpenko, *Fields of any $u$-invariant but a 2-power minus 1 or 3*,
  preprint, 5 August 2026,
  [author's web page](https://sites.ualberta.ca/~karpenko/publ/u1or3-02.pdf).
- [MerkurjevParimala2025] A. Merkurjev, R. Parimala, *Quadratic forms beyond arithmetic*, Notices
  Amer. Math. Soc. 72 (2025), no. 7, 711–718,
  [doi:10.1090/noti3192](https://doi.org/10.1090/noti3192).
-/

namespace KaplanskyUInvariant

open QuadraticForm

/-- `IsUInvariant n` means that some field of characteristic not `2` has $u$-invariant $n$, i.e.
$n$ is the largest dimension of an anisotropic quadratic form over that field. -/
def IsUInvariant (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)), IsGreatest (anisotropicDims F) n

/-- $u(\mathbb{C}) = 1$ [MerkurjevParimala2025, §5.1]: the form $x^2$ is anisotropic, and every
quadratic form in two or more variables over an algebraically closed field is isotropic. -/
@[category test, AMS 11 12]
theorem isGreatest_anisotropicDims_complex : IsGreatest (anisotropicDims ℂ) 1 := by
  refine ⟨one_mem_anisotropicDims ℂ, fun n ⟨Q, hQ, _⟩ ↦ ?_⟩
  by_contra! h
  have hsep : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft := fun x hx ↦
    hQ x (by simpa [QuadraticMap.associated_eq_self_apply] using hx x)
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed hsep
  have hm : 2 ≤ Module.finrank ℂ (Fin n → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact h
  generalize Module.finrank ℂ (Fin n → ℂ) = m at e hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  set v : Fin (k + 2) → ℂ := Fin.cons 1 (Fin.cons Complex.I 0) with hv
  have hv0 : QuadraticMap.weightedSumSquares ℂ (1 : Fin (k + 2) → ℂ) v = 0 := by
    simp [hv, Fin.sum_univ_succ, Complex.I_mul_I]
  have h0 : e.symm v = 0 := hQ _ (by rw [e.symm.map_app, hv0])
  have : v = 0 := e.symm.toLinearEquiv.map_eq_zero_iff.mp h0
  simpa [hv] using congr_fun this 0

/-- $u(\mathbb{R}) = \infty$ [MerkurjevParimala2025, §5.1]: the sum of $n$ squares is anisotropic
for every $n$, so there is no largest dimension of an anisotropic form. -/
@[category test, AMS 11 12]
theorem not_bddAbove_anisotropicDims_real : ¬ BddAbove (anisotropicDims ℝ) := by
  rw [anisotropicDims_eq_univ]
  exact not_bddAbove_univ

/--
**The values of the $u$-invariant**, stated as in [MerkurjevParimala2025, §5.1]: which integers
are $u$-invariants of fields (of characteristic not $2$)? The question goes back to
[Kaplansky1953], who conjectured that only powers of $2$ occur
(`u_invariant_values.variants.kaplansky_conjecture`). Every positive even integer is a
$u$-invariant (`u_invariant_values.variants.even`), $3$, $5$ and $7$ are not
(`u_invariant_values.variants.not_three`, `u_invariant_values.variants.not_five`,
`u_invariant_values.variants.not_seven`), and it is expected that every odd integer $\ge 9$ is
(`u_invariant_values.variants.odd`). Granting the preprint [Karpenko2026]
(`u_invariant_values.variants.karpenko`), the answer is known for every $n$ except $n = 2^r - 1$
and $n = 2^r - 3$ with $r \ge 4$.
-/
@[category research open, AMS 11 12]
theorem u_invariant_values :
    let S : Set ℕ := answer(sorry)
    ∀ n, n ∈ S ↔ IsUInvariant n := by
  sorry

/--
**Kaplansky's conjecture** [Kaplansky1953, p. 202]: the $u$-invariant of a field is a power of
$2$ whenever it is finite. Disproved by Merkurjev, who constructed a field of $u$-invariant $6$
[Merkurjev1989] (`u_invariant_values.variants.even`).
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.kaplansky_conjecture :
    answer(False) ↔ ∀ n, IsUInvariant n → ∃ k, n = 2 ^ k := by
  sorry

/-- The $u$-invariant is never $3$ [Kaplansky1953, Theorem 2]; see also
[Lam2005, Proposition XI.6.8] and [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_three : ¬ IsUInvariant 3 := by
  sorry

/-- The $u$-invariant is never $5$ [Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_five : ¬ IsUInvariant 5 := by
  sorry

/-- The $u$-invariant is never $7$ [Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_seven : ¬ IsUInvariant 7 := by
  sorry

/--
Every power of $2$ is a $u$-invariant [Kaplansky1953, p. 202]: Theorem 3 of [Kaplansky1953]
gives $u(F((t))) = 2u(F)$, so $u(\mathbb{C}((t_1)) \cdots ((t_k))) = 2^k$; see also
[EKM2008, §38].
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.two_pow (k : ℕ) : IsUInvariant (2 ^ k) := by
  sorry

/--
**Merkurjev's theorem** [Merkurjev1991], see also [EKM2008, Theorem 38.4]: every positive even
integer is a $u$-invariant. The case $6$, the first counterexample to Kaplansky's conjecture, is
[Merkurjev1989].
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.even (n : ℕ) (hn : Even n) (hn₀ : n ≠ 0) :
    IsUInvariant n := by
  sorry

/-- **Izhboldin's theorem** [Izhboldin2001]: there is a field of $u$-invariant $9$,
the first example of an odd $u$-invariant greater than $1$. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.nine : IsUInvariant 9 := by
  sorry

/-- **Vishik's theorem** [Vishik2009, Corollary 5.2]: for every $r \ge 3$ there is a field of
$u$-invariant $2^r + 1$. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.two_pow_add_one (r : ℕ) (hr : 3 ≤ r) :
    IsUInvariant (2 ^ r + 1) := by
  sorry

/--
**Karpenko's theorem** [Karpenko2026, Theorem 1.1]: if neither $n + 1$ nor $n + 3$ is a power
of $2$, then there is a field of $u$-invariant $n$. This covers every positive integer except
$1$, $3$, $5$, $7$ and the integers $2^r - 1$, $2^r - 3$ with $r \ge 4$. As of September 2026
the result is a preprint and not yet peer-reviewed.
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.karpenko (n : ℕ) (h₁ : ∀ r, 2 ^ r ≠ n + 1)
    (h₃ : ∀ r, 2 ^ r ≠ n + 3) : IsUInvariant n := by
  sorry

/--
The special case $n = 11$ of `u_invariant_values.variants.karpenko`, the first odd value not of
the form $2^r + 1$ shown to be a $u$-invariant; it was announced in the preprint
*Fields of $u$-invariant 11* (21 April 2026) that [Karpenko2026] absorbs.
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.eleven : IsUInvariant 11 := by
  sorry

/--
The expectation recorded in [MerkurjevParimala2025, §5.1]: every odd integer $\ge 9$ is a
$u$-invariant. By `u_invariant_values.variants.karpenko` this is open exactly for the integers
$2^r - 1$ and $2^r - 3$ with $r \ge 4$.
-/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.odd :
    answer(sorry) ↔ ∀ n, Odd n → 9 ≤ n → IsUInvariant n := by
  sorry

/-- The smallest open case of the form $2^r - 3$: is there a field of $u$-invariant $13$? -/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.thirteen : answer(sorry) ↔ IsUInvariant 13 := by
  sorry

/-- The smallest open case of the form $2^r - 1$: is there a field of $u$-invariant $15$? -/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.fifteen : answer(sorry) ↔ IsUInvariant 15 := by
  sorry

end KaplanskyUInvariant

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
# Erdős Problem 978

*Reference:*
 - [erdosproblems.com/978](https://www.erdosproblems.com/978)
 - [Ho67] Hooley, C., On the power free values of polynomials. Mathematika (1967), 21--26.
 - [Br11] Browning, T. D., Power-free values of polynomials. Arch. Math. (Basel) (2011), 139--150.
 - [Er53] Erdős, P., Arithmetical properties of polynomials. J. London Math. Soc. (1953), 416--425.
 - [OAI26a] OpenAI, *Squarefree values of quartics and power-free values of polynomials*. OpenAI
   Math Release preprint (2026).
   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf
-/

@[expose] public section

open Polynomial Set

namespace Erdos978

/-- Let `f ∈ ℤ[X]` be an irreducible polynomial with positive leading coefficient. Suppose that the
degree `k` of `f` is larger than `2` and is not equal to a power of `2`. Then the set of `n` such
that `f n` is `(k - 1)`-th power free is infinite, and this is proved in [Er53]. -/
@[category research solved, AMS 11]
theorem erdos_978.variants.sub_one {f : ℤ[X]} (hi : Irreducible f) (hd : 2 < f.natDegree)
    (hp : ∀ (x : ℕ), f.natDegree ≠ 2 ^ x) (hlc : 0 < f.leadingCoeff) :
    {n : ℕ | Powerfree (f.natDegree - 1) (f.eval (n : ℤ))}.Infinite := by
  sorry

/-- Let `f ∈ ℤ[X]` be an irreducible polynomial with positive leading coefficient. Suppose that the
degree `k` of `f` is larger than `2`, is not equal to a power of `2`, and `f n` has no fixed
`(k - 1)`-th power divisors other than `1`. Then the set of `n` such that `f n` is `(k - 1)`-th
power free has positive density, and this is proved in [Ho67]. -/
@[category research solved, AMS 11]
theorem erdos_978.parts.i {f : ℤ[X]} (hi : Irreducible f) (hd : 2 < f.natDegree)
    (hp2 : ∀ (x : ℕ), f.natDegree ≠ 2 ^ x) (hlc : 0 < f.leadingCoeff)
    (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)) :
    HasPosDensity {n : ℕ | Powerfree (f.natDegree - 1) (f.eval (n : ℤ))} := by
  sorry

/-- If the degree `k` of `f` is larger than or equal to `9`, and `f n` has no fixed `(k - 2)`-th
power divisors other than `1`, then the set of `n` such that `f n` is `(k - 2)`-th power free has
infinitely many elements. This result is proved in [Br11]. -/
@[category research solved, AMS 11]
theorem erdos_978.variants.sub_two {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree)
    (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $k > 3$ (and $k \neq 2^l$), then are there infinitely many $n$ for which $f(n)$ is
$(k-2)$-power-free?

This was disproved by the DeepMind prover agent.
-/
@[category research solved, question, AMS 11,
formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/3b5d6ac2555cd63b83d418c29ff040876be9dee0/FormalConjectures/ErdosProblems/978.lean#L64"]
theorem erdos_978.variants.allow_fixed_divisors :
    ¬ ∀ {f : ℤ[X]}, Irreducible f → f.natDegree > 3 →
    (¬ ∃ l : ℕ, f.natDegree = 2 ^ l) → 0 < f.leadingCoeff →
    (¬ ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)) →
    {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
If $k>3$ (and $k \neq 2^l$), and for all primes $p$ there exists $n$ such that $p^{k-2}\nmid f(n)$,
then are there infinitely many $n$ for which $f(n)$ is $(k-2)$-power-free?

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof,
which gives positive density and does not need $k \neq 2^l$ or a positive leading coefficient.
The linked statement is `erdos_978.variants.all_degrees`; see `erdos_978_ii_of_all_degrees`.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/Main.lean#L144"]
theorem erdos_978.parts.ii :
    ∀ {f : ℤ[X]}, Irreducible f → f.natDegree > 3 →
    (¬ ∃ l : ℕ, f.natDegree = 2 ^ l) → 0 < f.leadingCoeff →
    (∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) →
    {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Does `n ^ 4 + 2` represent infinitely many squarefree numbers?

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof,
which gives positive density for every irreducible quartic with no fixed square divisor; see
`erdos_978_iii_of_all_degrees`. -/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/Main.lean#L144"]
theorem erdos_978.parts.iii : {n : ℕ | Squarefree (n ^ 4 + 2)}.Infinite := by
  sorry

/- The definitions in `Density` are copied from the Lean statement linked at
`erdos_978.parts.ii`. `count f k X` is the number of `n ∈ [1, X]` with `f(n)` `k`-th power
free, and `rho f q` is the number of residues `a mod q` with `q ∣ f(a)`. -/

namespace Density

/-- No prime `k`-th power divides `a`. -/
def PowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ k ∣ a

/-- The number of residues `a mod q` with `q ∣ f(a)`. -/
def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)).card

/-- The number of `n ∈ [1, X]` with `f(n)` `k`-th power free. -/
noncomputable def count (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ => PowerFree k (f.eval (n : ℤ))).card

/-- No prime `k`-th power divides all values of `f`. -/
def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

/-- The local density at the prime `p`. -/
noncomputable def localFactor (f : Polynomial ℤ) (k : ℕ) (p : Nat.Primes) : ℝ :=
  1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k

/-- The product of the local densities. -/
noncomputable def densityConstant (f : Polynomial ℤ) (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, localFactor f k p

open Filter Asymptotics in
/-- The product of the local densities converges to a positive constant `c`, and
`count f k X = c X + o(X)`. -/
def DensityStatement (f : Polynomial ℤ) (k : ℕ) : Prop :=
  Multipliable (localFactor f k) ∧
  0 < densityConstant f k ∧
  (fun X : ℝ => (count f k X : ℝ) - densityConstant f k * X) =o[atTop]
    (fun X : ℝ => X)

/-- `PowerFree` implies `Powerfree`: an integer that is not a unit has a prime factor. -/
@[category API, AMS 11]
lemma powerfree_of_powerFree {k : ℕ} {a : ℤ} (h : PowerFree k a) : Powerfree k a := by
  intro x hx
  by_contra hu
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd fun h1 => hu (Int.isUnit_iff_natAbs_eq.mpr h1)
  exact h p hp ((pow_dvd_pow_of_dvd (Int.natCast_dvd.mpr hpx) k).trans hx)

/-- If for every prime `p` some value of `f` is not divisible by `p ^ k`, then `f` is locally
admissible: that value modulo `p ^ k` is a residue not counted by `rho`. -/
@[category API, AMS 11]
lemma locallyAdmissible_of_forall_exists {f : ℤ[X]} {k : ℕ}
    (h : ∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ k ∣ f.eval (n : ℤ)) :
    LocallyAdmissible f k := by
  intro p hp
  obtain ⟨n, hn⟩ := h p hp
  have hq : 0 < p ^ k := pow_pos hp.pos k
  rw [rho]
  calc _ < (Finset.range (p ^ k)).card := by
        refine Finset.card_lt_card (Finset.filter_ssubset.mpr
          ⟨n % p ^ k, Finset.mem_range.mpr (Nat.mod_lt _ hq), fun hdvd => hn ?_⟩)
        have h1 := sub_dvd_eval_sub (n : ℤ) ((n % p ^ k : ℕ) : ℤ) f
        have h2 : (p : ℤ) ^ k ∣ (n : ℤ) - ((n % p ^ k : ℕ) : ℤ) := by
          have := (Int.mod_modEq (n : ℤ) ((p : ℤ) ^ k)).dvd
          push_cast
          exact this
        have h3 : (p : ℤ) ^ k ∣ f.eval ((n % p ^ k : ℕ) : ℤ) := by exact_mod_cast hdvd
        simpa using dvd_add (h2.trans h1) h3
    _ = p ^ k := Finset.card_range _

/-- A positive density gives infinitely many `n` with `f(n)` power free. -/
@[category API, AMS 11]
lemma infinite_of_densityStatement {f : ℤ[X]} {k : ℕ} (h : DensityStatement f k) :
    {n : ℕ | PowerFree k (f.eval (n : ℤ))}.Infinite := by
  obtain ⟨-, hc, ho⟩ := h
  intro hfin
  set c := densityConstant f k
  have hbound : ∀ Y : ℝ, count f k Y ≤ hfin.toFinset.card := by
    classical
    intro Y
    rw [count]
    refine Finset.card_le_card fun n hn => ?_
    rw [Set.Finite.mem_toFinset]
    exact (Finset.mem_filter.mp hn).2
  set M : ℝ := (hfin.toFinset.card : ℝ)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp (ho.def (half_pos hc))
  have hM : 0 ≤ M := Nat.cast_nonneg _
  set Y := max Y₀ (2 * (M + 1) / c)
  have hY := hY₀ Y (le_max_left _ _)
  have hYc : 2 * (M + 1) ≤ Y * c := (div_le_iff₀ hc).mp (le_max_right _ _)
  have hYpos : 0 < Y := lt_of_lt_of_le (div_pos (by linarith) hc) (le_max_right _ _)
  simp only [Real.norm_eq_abs] at hY
  rw [abs_of_pos hYpos] at hY
  have h1 := neg_abs_le ((count f k Y : ℝ) - c * Y)
  have h2 : (count f k Y : ℝ) ≤ M := Nat.cast_le.mpr (hbound Y)
  nlinarith

end Density

set_option linter.style.formal_proof_palomar false in
/--
The theorem of [OAI26a], stated with the definitions of the linked Lean proof: if `f ∈ ℤ[X]`
is irreducible over `ℚ`, has degree `k ≥ 4`, and no prime `(k - 2)`-th power divides all of
its values, then the `n` with `f(n)` `(k - 2)`-th power free have a positive density.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/Main.lean#L144"]
theorem erdos_978.variants.all_degrees (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree)
    (hlocal : Density.LocallyAdmissible f (f.natDegree - 2)) :
    Density.DensityStatement f (f.natDegree - 2) := by
  sorry

/-- The theorem of [OAI26a] answers `erdos_978.parts.ii`: an irreducible `f ∈ ℤ[X]` of positive
degree stays irreducible over `ℚ` (Gauss's lemma), and a positive density gives infinitely
many `n`. -/
@[category test, AMS 11]
theorem erdos_978_ii_of_all_degrees (h : type_of% erdos_978.variants.all_degrees) :
    type_of% @erdos_978.parts.ii := by
  intro f hi hd _ _ hp
  have hirr : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive (by omega))).mp hi
  exact (Density.infinite_of_densityStatement
    (h f hirr (by omega) (Density.locallyAdmissible_of_forall_exists hp))).mono
    fun n hn => Density.powerfree_of_powerFree hn

/-- The theorem of [OAI26a] for $f = X^4 + 2$ answers `erdos_978.parts.iii`: `f` is irreducible
by Eisenstein's criterion at `2`, and `p ^ 2 ∤ f(0) = 2` for every prime `p`. -/
@[category test, AMS 11]
theorem erdos_978_iii_of_all_degrees (h : type_of% erdos_978.variants.all_degrees) :
    type_of% erdos_978.parts.iii := by
  set f : ℤ[X] := X ^ 4 + C 2 with hf
  have hdeg : f.natDegree = 4 := natDegree_X_pow_add_C
  have hmonic : f.Monic := monic_X_pow_add_C 2 (by norm_num)
  have hirr : Irreducible f := by
    have hP : (Ideal.span {(2 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
    have hdegree : f.degree = 4 := degree_X_pow_add_C (by norm_num) 2
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hmonic.isPrimitive
    · rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
      norm_num
    · intro n hn
      rw [hdegree] at hn
      have hn4 : n < 4 := by exact_mod_cast hn
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> simp [hf, coeff_X_pow]
    · rw [hdegree]
      norm_num
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp [hf]
  have hq : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp hirr
  have hloc : Density.LocallyAdmissible f (f.natDegree - 2) := by
    refine Density.locallyAdmissible_of_forall_exists fun p hp => ⟨0, fun hdvd => ?_⟩
    have h0 : f.eval ((0 : ℕ) : ℤ) = 2 := by simp [hf]
    rw [hdeg, h0] at hdvd
    have hle := Int.le_of_dvd (by norm_num) hdvd
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    norm_num at hle
    nlinarith
  refine (Density.infinite_of_densityStatement (h f hq (by omega) hloc)).mono fun n hn => ?_
  have hsq : Squarefree (f.eval (n : ℤ)) := by
    simpa [hdeg] using Density.powerfree_of_powerFree hn
  show Squarefree (n ^ 4 + 2)
  rw [← Int.squarefree_natCast]
  push_cast
  simpa [hf] using hsq

end Erdos978

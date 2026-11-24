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
# Natural density of Størmer numbers

A positive integer $n \ge 1$ is a *Størmer number* (`OEIS A005528`) if $n^2 + 1$ admits a prime
divisor $p \ge 2n$, i.e., $(n^2 + 1).\text{maxPrimeFac} \ge 2n$. Carl Størmer introduced these
integers in studying finite Gregory-series decompositions of rational arctangents. John Todd
`[To49]` proved that both the Størmer numbers and their positive-integer complement are infinite.
Everest and Harman `[EH08, Theorem 1.4 and Conjecture 1.5]` proved that the lower and upper
asymptotic densities of `{n | IsStormerNumber n}` lie in $[0.5324, 0.905]$, and conjectured a
natural density of $\log 2$.

*References:*
- [Wikipedia: Størmer number](https://en.wikipedia.org/wiki/St%C3%B8rmer_number)
- [OEIS A005528](https://oeis.org/A005528)
- `[To49]` J. Todd, *A problem on arc tangent relations*, Amer. Math. Monthly **56** (1949), no. 8,
  517–528.
- `[EH08]` G. Everest and G. Harman, *On primitive divisors of $n^2 + b$*, in *Number Theory and
  Polynomials*, LMS Lecture Note Ser. **352**, Cambridge Univ. Press, 2008, 142–154,
  https://doi.org/10.1017/CBO9780511721274.011.
-/

@[expose] public section

namespace StormerNumber

/-- Predicate for Størmer numbers: $n \ge 1$ with `2 * n ≤ (n ^ 2 + 1).maxPrimeFac`. -/
def IsStormerNumber (n : ℕ) : Prop :=
  1 ≤ n ∧ 2 * n ≤ (n ^ 2 + 1).maxPrimeFac

instance instDecidablePredIsStormerNumber : DecidablePred IsStormerNumber :=
  fun n => by
    unfold IsStormerNumber
    infer_instance

/-- Zero is excluded from `IsStormerNumber` by positivity. -/
@[category test, AMS 11]
theorem not_isStormerNumber_zero : ¬ IsStormerNumber 0 := by
  decide

/-- Checks `IsStormerNumber` on $[0, 20]$ against `OEIS A005528` (excluding $0, 3, 7, 8, 13, 17,
18$). -/
@[category test, AMS 11]
theorem stormerNumber_up_to_twenty :
    (List.range 21).filter (fun n => decide (IsStormerNumber n)) =
      [1, 2, 4, 5, 6, 9, 10, 11, 12, 14, 15, 16, 19, 20] := by
  decide +kernel

/-- Any positive integer $n$ with $n^2 + 1$ prime is a Størmer number. -/
@[category API, AMS 11]
theorem isStormerNumber_of_prime_sq_add_one {n : ℕ} (hn : 1 ≤ n) (hp : (n ^ 2 + 1).Prime) :
    IsStormerNumber n := by
  refine ⟨hn, ?_⟩
  rw [hp.maxPrimeFac_eq_self]
  nlinarith

/--
Infinitely many positive integers are Størmer numbers `[To49]`.
-/
@[category research solved, AMS 11]
theorem stormer_numbers_infinite : {n : ℕ | IsStormerNumber n}.Infinite := by
  sorry

/--
Infinitely many positive integers fail `IsStormerNumber` `[To49]`, proved inline via the Sophie
Germain factorization $(2m^2)^2 + 1 = (2m^2 - 2m + 1)(2m^2 + 2m + 1)$ at $m = k + 2$.
-/
@[category research solved, AMS 11]
theorem non_stormer_numbers_infinite : {n : ℕ | 1 ≤ n ∧ ¬ IsStormerNumber n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * (k + 2) ^ 2)
    (fun a b hab => by nlinarith) fun k => ?_
  have hk : 2 * (k + 2) + 4 ≤ 2 * (k + 2) ^ 2 := by nlinarith
  refine ⟨by omega, ?_⟩
  rintro ⟨-, hle⟩
  set m := (2 * (k + 2) ^ 2) ^ 2 + 1
  have hm : 1 < m := by dsimp [m]; nlinarith
  have hp : m.maxPrimeFac.Prime := Nat.prime_maxPrimeFac_of_one_lt m hm
  have hfac : m = (2 * (k + 2) ^ 2 - 2 * (k + 2) + 1) * (2 * (k + 2) ^ 2 + 2 * (k + 2) + 1) := by
    dsimp [m]; zify [show 2 * (k + 2) ≤ 2 * (k + 2) ^ 2 by omega]; ring
  have hdvd : m.maxPrimeFac ∣
      (2 * (k + 2) ^ 2 - 2 * (k + 2) + 1) * (2 * (k + 2) ^ 2 + 2 * (k + 2) + 1) :=
    hfac ▸ Nat.maxPrimeFac_dvd
  rcases hp.dvd_mul.mp hdvd with h1 | h2
  · have := Nat.le_of_dvd (by omega) h1; omega
  · have := Nat.le_of_dvd (by omega) h2; omega

/--
Everest–Harman lower density bound `[EH08, Theorem 1.4]`: the set `{n | IsStormerNumber n}` has
lower asymptotic density at least $0.5324$.
-/
@[category research solved, AMS 11]
theorem everest_harman_stormer_lowerDensity :
    (5324 / 10000 : ℝ) ≤ {n : ℕ | IsStormerNumber n}.lowerDensity := by
  sorry

/--
Everest–Harman upper density bound `[EH08, Theorem 1.4]`: the set `{n | IsStormerNumber n}` has
upper asymptotic density at most $0.905$.
-/
@[category research solved, AMS 11]
theorem everest_harman_stormer_upperDensity :
    {n : ℕ | IsStormerNumber n}.upperDensity ≤ (905 / 1000 : ℝ) := by
  sorry

/--
Everest–Harman Størmer density conjecture `[EH08, Conjecture 1.5]`: the set of Størmer numbers has
natural density $\log 2$.
-/
@[category research open, AMS 11]
theorem everest_harman_stormer_density_conjecture :
    {n : ℕ | IsStormerNumber n}.HasDensity (Real.log 2) := by
  sorry

/--
Existence of the natural density of Størmer numbers: a weaker consequence of
`everest_harman_stormer_density_conjecture`. While `[EH08, Theorem 1.4]` bounds the lower and upper
densities in $[0.5324, 0.905]$ (`everest_harman_stormer_lowerDensity` and
`everest_harman_stormer_upperDensity`), convergence of the natural density remains open.
-/
@[category research open, AMS 11]
theorem everest_harman_stormer_density_conjecture.variants.exists_density :
    ∃ d : ℝ, {n : ℕ | IsStormerNumber n}.HasDensity d := by
  sorry

end StormerNumber

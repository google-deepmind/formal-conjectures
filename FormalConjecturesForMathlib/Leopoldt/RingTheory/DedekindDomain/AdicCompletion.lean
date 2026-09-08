/-
Copyright 2025 The Formal Conjectures Authors.

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
public import Mathlib

/-!
# Congruences and convergence in the adic completions above `p`

The dictionary between divisibility by powers of `p` in `𝓞 K` and convergence in the completions
`K_𝔭` at the primes `𝔭 ∣ p`: a sequence of algebraic integers is eventually `1` modulo every
power of `p` exactly when it tends to `1` in every such completion.

Staging area: kept in the `Leopoldt` namespace. Narrow the imports and pick final namespaces
before upstreaming.
-/

@[expose] public section

open Filter IsDedekindDomain NumberField

open scoped NumberField

namespace Leopoldt

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

lemma coe_coe_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ((x : K) : v.adicCompletion K) = algebraMap (𝓞 K) (v.adicCompletion K) x := rfl

lemma valued_algebraMap (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) x) = v.intValuation x := by
  rw [← coe_coe_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

omit [Fact p.Prime] in
lemma intValuation_le_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : (p : 𝓞 K) ∈ v.asIdeal)
    {x : 𝓞 K} {M : ℕ} (hx : (p : 𝓞 K) ^ M ∣ x) : v.intValuation x ≤ WithZero.exp (-M : ℤ) := by
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le]
  refine (Ideal.span_singleton_le_span_singleton.2 hx).trans ?_
  rw [← Ideal.span_singleton_pow]
  exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hv) M

omit [Fact p.Prime] in

/-- A sequence of algebraic integers which is eventually `1` modulo every power of `p` tends
to `1` in each completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$. -/
lemma tendsto_of_forall_eventually_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : (p : 𝓞 K) ∈ v.asIdeal)
    {f : ℕ → 𝓞 K} (hf : ∀ M : ℕ, ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ f n - 1) :
    Tendsto (fun n ↦ ((f n : K) : v.adicCompletion K)) atTop (nhds 1) := by
  refine Filter.tendsto_def.2 fun s hs ↦ ?_
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have hg0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := (map_ne_zero _).2 γ.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.val = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hg0).symm⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, WithZero.exp (-M : ℤ) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.val := by
    refine ⟨(-k).toNat + 1, ?_⟩
    rw [hk, WithZero.exp_lt_exp]
    have := Int.self_le_toNat (-k)
    omega
  filter_upwards [hf M] with n hn
  refine hγ ?_
  show Valued.v.restrict (((f n : K) : v.adicCompletion K) - 1) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding, coe_coe_adicCompletion,
    ← map_one (algebraMap (𝓞 K) (v.adicCompletion K)), ← map_sub, valued_algebraMap]
  exact (intValuation_le_of_dvd hv hn).trans_lt hM

/-- Divisibility by `p ^ M` in `𝓞 K` follows from divisibility by a large enough power of every
prime above `p`. -/
lemma exists_forall_dvd_of_forall_pow_dvd (M : ℕ) : ∃ M' : ℕ, ∀ x : 𝓞 K,
    (∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v.asIdeal ^ M' ∣ Ideal.span {x}) →
    (p : 𝓞 K) ^ M ∣ x := by
  classical
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hI0 : Ideal.span {(p : 𝓞 K) ^ M} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero M hp0
  refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span {(p : 𝓞 K) ^ M})), fun x hx ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact dvd_zero _
  have hJ0 : Ideal.span {x} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx0
  rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.dvd_iff_le,
    UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI0 hJ0,
    Multiset.le_iff_count]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : 𝓞 K) ^ M})
  · have hqp : Prime q := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
    have hqP : q.IsPrime := (Ideal.prime_iff_isPrime hqp.ne_zero).1 hqp
    have hpq : (p : 𝓞 K) ∈ q := by
      have := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
      rw [← Ideal.span_singleton_pow] at this
      exact Ideal.dvd_span_singleton.1 (hqp.dvd_of_dvd_pow this)
    have := hx ⟨q, hqP, hqp.ne_zero⟩ hpq
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hqp.irreducible hJ0,
      normalize_eq, Nat.cast_le] at this
    exact (Multiset.count_le_card _ _).trans this
  · rw [Multiset.count_eq_zero.2 hq]
    exact Nat.zero_le _

/-- A sequence of algebraic integers which tends to `1` in every completion $K_\mathfrak{p}$ with
$\mathfrak{p} \mid p$ is eventually `1` modulo every power of `p`. -/
lemma eventually_dvd_of_tendsto {f : ℕ → 𝓞 K}
    (hf : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal →
      Tendsto (fun n ↦ ((f n : K) : v.adicCompletion K)) atTop (nhds 1)) (M : ℕ) :
    ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ f n - 1 := by
  obtain ⟨M', hM'⟩ := exists_forall_dvd_of_forall_pow_dvd (K := K) (p := p) M
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hS : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 K)}) ?_).subset fun v hv ↦ ?_
    · rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hp0
    · exact Ideal.dvd_span_singleton.2 hv
  have : ∀ᶠ n in atTop, ∀ v ∈ {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal},
      v.asIdeal ^ M' ∣ Ideal.span {f n - 1} := by
    rw [Filter.eventually_all_finite hS]
    intro v hv
    have hx₀ : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) ((p : 𝓞 K) ^ M')) ≠ 0 := by
      rw [valued_algebraMap]
      exact HeightOneSpectrum.intValuation_ne_zero v _ (pow_ne_zero _ hp0)
    have hγ : Valued.v.restrict (algebraMap (𝓞 K) (v.adicCompletion K) ((p : 𝓞 K) ^ M')) ≠ 0 :=
      fun h ↦ hx₀ (by simpa using congrArg MonoidWithZeroHom.ValueGroup₀.embedding h)
    have hs : {y : v.adicCompletion K | Valued.v.restrict (y - 1) <
        Valued.v.restrict (algebraMap (𝓞 K) (v.adicCompletion K) ((p : 𝓞 K) ^ M'))} ∈
        nhds (1 : v.adicCompletion K) :=
      Valued.mem_nhds.2 ⟨Units.mk0 _ hγ, subset_rfl⟩
    filter_upwards [(hf v hv).eventually_mem hs] with n hn
    rw [Valuation.restrict_lt_iff, coe_coe_adicCompletion,
      ← map_one (algebraMap (𝓞 K) (v.adicCompletion K)), ← map_sub, valued_algebraMap,
      valued_algebraMap] at hn
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    exact hn.le.trans (intValuation_le_of_dvd hv dvd_rfl)
  filter_upwards [this] with n hn
  exact hM' _ fun v hv ↦ hn v hv

end Leopoldt

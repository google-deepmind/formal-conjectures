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
# Erdős Problem 820

*References:*
- [erdosproblems.com/820](https://www.erdosproblems.com/820)
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974),
  197-202.
- [OEIS A263647](https://oeis.org/A263647): the $n$ with $(2^n-1, 3^n-1) = 1$.
-/

@[expose] public section

open Filter

namespace Erdos820

/-- $H(n)$ is the smallest integer $l$ such that there is some $k < l$ with
$(k^n-1, l^n-1) = 1$.

We take $k$ and $l$ to be integers with $k \geq 2$, so that $k^n - 1 \geq 1$ for $n \geq 1$.
Smaller $k$ give degenerate values: over the integers $k = 0$ gives $(-1, l^n-1) = 1$, and $k = 1$
gives $(0, l^n-1) = l^n-1$, which is $1$ for $n = 1$, $l = 2$. Both would contradict the value
$H(1) = 3$ listed in the source.

For $n \geq 1$ the set is nonempty (see `Erdos820.H_spec`). For $n = 0$ it is empty, and
`H 0 = 0` by the `sInf ∅` convention; the only statement whose truth depends on `H 0` is
`Erdos820.H_eq_three_iff`, where both sides are false. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}

/-- $K(n)$ is the smallest integer $k \geq 2$ such that $(k^n-1, 2^n-1) = 1$. As for
`Erdos820.H`, smaller $k$ are excluded because they give degenerate values.

For $n \geq 2$ the value $k = 2$ never works, and $k = 2^n - 1$ always works. For $n = 1$ we
get $K(1) = 2$, and for $n = 0$ the set is empty, so `K 0 = 0`. -/
noncomputable def K (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (2 ^ n - 1)}

/-- For $n \geq 1$ the minimum defining $H(n)$ is attained: there is $k$ with $2 \leq k < H(n)$
and $(k^n-1, H(n)^n-1) = 1$. For $n \geq 2$, the pair $k = 2$, $l = 2^n - 1$ shows that the set
is nonempty. For $n = 1$, take $k = 2$, $l = 3$. -/
@[category API, AMS 11]
theorem H_spec {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1) := by
  have hne : {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}.Nonempty := by
    obtain rfl | hn2 := hn.eq_or_lt
    · exact ⟨3, 2, le_rfl, by norm_num, by decide⟩
    · have h4 : 4 ≤ 2 ^ n :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      refine ⟨2 ^ n - 1, 2, le_rfl, by omega, ?_⟩
      have h1 : 1 ≤ (2 ^ n - 1) ^ n := Nat.one_le_pow _ _ (by omega)
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self _ (by omega))
        ((Nat.coprime_self_sub_right h1).2 (Nat.coprime_one_right _))
  exact Nat.sInf_mem hne

/-- $H(n) = 3$ if and only if $(2^n-1, 3^n-1) = 1$. This holds for every $n$, including
$n = 0$, where both sides are false. -/
@[category API, AMS 11]
theorem H_eq_three_iff (n : ℕ) : H n = 3 ↔ Nat.Coprime (2 ^ n - 1) (3 ^ n - 1) := by
  constructor
  · intro h
    have hne : {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}.Nonempty :=
      Nat.nonempty_of_pos_sInf (by unfold H at h; omega)
    have hmem : H n ∈ {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)} :=
      Nat.sInf_mem hne
    rw [h] at hmem
    obtain ⟨k, hk2, hk3, hk⟩ := hmem
    obtain rfl : k = 2 := by omega
    exact hk
  · intro h
    unfold H
    refine le_antisymm (Nat.sInf_le ⟨2, le_rfl, by norm_num, h⟩)
      (le_csInf ⟨3, 2, le_rfl, by norm_num, h⟩ ?_)
    rintro l ⟨k, hk2, hkl, -⟩
    omega

/-- The first values of $H(n)$, for $1 \leq n \leq 10$, are $3, 3, 3, 6, 3, 18, 3, 6, 3, 12$. -/
@[category test, AMS 11]
theorem H_one_to_ten :
    H 1 = 3 ∧ H 2 = 3 ∧ H 3 = 3 ∧ H 4 = 6 ∧ H 5 = 3 ∧ H 6 = 18 ∧ H 7 = 3 ∧ H 8 = 6 ∧
      H 9 = 3 ∧ H 10 = 12 := by
  sorry

/--
Let $H(n)$ be the smallest integer $l$ such that there exists $k < l$ with $(k^n-1, l^n-1) = 1$.
Is it true that $H(n) = 3$ infinitely often? That is, is $(2^n-1, 3^n-1) = 1$ for infinitely
many $n$ (see `Erdos820.H_eq_three_iff`)?

The request to estimate $H(n)$ is open-ended and not formalised; the variants below state the
specific questions that are asked. See also Erdős Problem 770.
-/
@[category research open, question, AMS 11]
theorem erdos_820 : {n : ℕ | H n = 3}.Infinite := by
  sorry

/--
Is it true that there exists some constant $c > 0$ such that, for all $\epsilon > 0$,
$$
H(n) > \exp\left(n^{(c-\epsilon)/\log\log n}\right)
$$
for infinitely many $n$ and
$$
H(n) < \exp\left(n^{(c+\epsilon)/\log\log n}\right)
$$
for all large enough $n$?
-/
@[category research open, question, AMS 11]
theorem erdos_820.variants.log_log_exponent :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ),
      (∃ᶠ n : ℕ in atTop,
        Real.exp ((n : ℝ) ^ ((c - ε) / Real.log (Real.log (n : ℝ)))) < (H n : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        (H n : ℝ) < Real.exp ((n : ℝ) ^ ((c + ε) / Real.log (Real.log (n : ℝ)))) := by
  sorry

/--
Let $K(n)$ be the smallest $k$ such that $(k^n-1, 2^n-1) = 1$. Does a similar upper bound hold
for $K(n)$? That is, is there a constant $c > 0$ such that, for all $\epsilon > 0$,
$$
K(n) < \exp\left(n^{(c+\epsilon)/\log\log n}\right)
$$
for all large enough $n$?

We read "similar" as an upper bound of the same shape, with its own constant $c$, which need
not be the same as in `Erdos820.erdos_820.variants.log_log_exponent`.
-/
@[category research open, question, AMS 11]
theorem erdos_820.variants.two_pow_upper :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (K n : ℝ) < Real.exp ((n : ℝ) ^ ((c + ε) / Real.log (Real.log (n : ℝ)))) := by
  sorry

/--
Erdős [Er74b] proved that there exists a constant $c > 0$ such that
$$
H(n) > \exp\left(n^{c/(\log\log n)^2}\right)
$$
for infinitely many $n$.
-/
@[category research solved, AMS 11]
theorem erdos_820.variants.erdos_lower :
    ∃ c > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)) ^ 2)) < (H n : ℝ) := by
  sorry

end Erdos820

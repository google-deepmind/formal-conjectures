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
# Erdős Problem 367

*References:*
- [erdosproblems.com/367](https://www.erdosproblems.com/367)
- [ErGr80] P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, L'Enseignement Mathématique (1980).
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos367

/--
`B r n` is the $r$-full part of $n$: the product of prime powers $p^a \| n$ with $a \geq r$.
-/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

/--
Let $B_2(n)$ be the $2$-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is the product of all
primes that divide $n$ exactly once). Is it true that, for every fixed $k \geq 1$,
$\prod_{n \leq m < n+k} B_2(m) \ll n^{2+o(1)}$?
-/
@[category research open, question, AMS 11]
theorem erdos_367.parts.i : ∀ k : ℕ, 1 ≤ k →
    ∃ e : ℕ → ℝ,
      e =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop,
        ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 + e n) := by
  sorry

/--
Or perhaps even $\prod_{n \leq m < n+k} B_2(m) \ll_k n^2$?

van Doorn notes in the comments that this fails for all $k \geq 3$.
-/
@[category research solved, question, AMS 11]
theorem erdos_367.parts.ii : ¬ ∀ k : ℕ, 1 ≤ k →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  sorry

/-- $B_r(m)$ divides $m$ for $m \neq 0$. -/
@[category API, AMS 11]
private lemma B_dvd (r : ℕ) {m : ℕ} (hm : m ≠ 0) : B r m ∣ m := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- $B_r(m) \le m + 1$ for every $m$. -/
@[category API, AMS 11]
private lemma B_le_succ (r m : ℕ) : B r m ≤ m + 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [B]
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (B_dvd r hm)).trans (Nat.le_succ m)

/-- For $k \le 2$, $\prod_{n \le m < n+k} B_2(m) \le (n + 2)^2$. -/
@[category API, AMS 11]
private lemma prod_B_le {k : ℕ} (hk : k ≤ 2) (n : ℕ) :
    ∏ m ∈ .Ico n (n + k), B 2 m ≤ (n + 2) ^ 2 := by
  calc ∏ m ∈ .Ico n (n + k), B 2 m ≤ (n + 2) ^ (Finset.Ico n (n + k)).card :=
        Finset.prod_le_pow_card _ _ _ fun m hm => by
          have := (Finset.mem_Ico.mp hm).2
          have := B_le_succ 2 m
          omega
    _ ≤ (n + 2) ^ 2 := by
        rw [Nat.card_Ico, Nat.add_sub_cancel_left]
        exact Nat.pow_le_pow_right (by omega) hk

/--
van Doorn notes in the comments that for $k \leq 2$ we trivially have
$\prod_{n \leq m < n+k} B_2(m) \ll n^2$.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro k hk
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h1 := prod_B_le hk n
  have h2 : ((n + 2) ^ 2 : ℕ) ≤ 4 * n ^ 2 := by nlinarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast h1.trans h2

/--
But this fails for all $k \geq 3$, and in fact
$\prod_{n \leq m < n+3} B_2(m) \gg n^2 \log n$ infinitely often.
-/
@[category research solved, AMS 11]
theorem erdos_367.variants.k_ge_three_lower :
    ∃ c > (0 : ℝ), ∃ᶠ (n : ℕ) in atTop,
      c * ((n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        ((∏ m ∈ .Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
It would also be interesting to find upper and lower bounds for the analogous product with $B_r$
for $r \geq 3$, where $B_r(n)$ is the $r$-full part of $n$ (that is, the product of prime powers
$p^a \mid n$ such that $p^{a+1} \nmid n$ and $a \geq r$). Is it true that, for every fixed
$r \geq 3$ and $k \geq 2$, there is some $\epsilon = \epsilon(r, k) > 0$ with
$\limsup \frac{\prod_{n \leq m < n+k} B_r(m)}{n^{1+\epsilon}} = \infty$?

The webpage writes "for every fixed $r,k \geq 2$ and $\epsilon > 0$", but van Doorn observes in
the [comments](https://www.erdosproblems.com/forum/thread/367#post-1766) that the intended
reading lets $\epsilon$ depend on $r$ and $k$. Since $B_r(m) \mid m$, the product is at most
$\prod_{n \leq m < n+k} m$, so the reading with $\epsilon$ universally quantified is false.

The answer is yes: $\epsilon = 1/(2r)$ works. For $j \geq r$ let $x = 2^j + 1$ and $n = x^r - 1$;
then $B_r(n+1) = x^r$ and $2^j \mid n$ gives $B_r(n) \geq 2^j$, so the product over $[n, n+k)$ is at
least $2^j x^r \geq (\sqrt{x}/2)\, n^{1 + 1/(2r)}$, which is unbounded. A stronger exponent
(any $\epsilon < (r+1)/r^2$) is claimed in the [forum](https://www.erdosproblems.com/forum/thread/367)
but is not formalised.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/kusasyu36/erdos367-higher-full-parts/blob/9c995fbb1ec62bd675ac9bc162f9e2337d6db4f9/Erdos367HigherFullParts.lean#L57"]
theorem erdos_367.variants.higher_full_parts :
    ∀ r k : ℕ, 3 ≤ r → 2 ≤ k → ∃ ε : ℝ, 0 < ε ∧
      atTop.limsup (fun n ↦
        ((∏ m ∈ .Ico n (n + k), B r m : ℕ) / (n : ℝ) ^ (1 + ε) |>.toEReal)) = ⊤ := by
  sorry

end Erdos367

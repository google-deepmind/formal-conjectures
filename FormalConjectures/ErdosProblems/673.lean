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
# Erdős Problem 673

*References:*
- [erdosproblems.com/673](https://www.erdosproblems.com/673)
- [Er79e] Erdős, Paul, _Some unconventional problems in number theory_. Astérisque (1979), 73-82.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
-/

@[expose] public section

open Filter Asymptotics Real

namespace Erdos673

/-- If $1=d_1<\cdots <d_{\tau(n)}=n$ are the divisors of $n$ (here `Nat.nth (· ∣ n) i` is
$d_{i+1}$), then
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$ -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

set_option linter.style.formal_proof_palomar false in
/--
Let $1=d_1<\cdots <d_{\tau(n)}=n$ be the divisors of $n$ and
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$
Is it true that $G(n)\to \infty$ for almost all $n$?

The answer is yes: Tao observed that $\tau(n/m)/m\leq G(n)\leq \tau(n)$ for any $m\mid n$ with
$m>1$, so that $G(n)$ behaves very similarly to $\tau(n)$. In [Er82e] Erdős recalls this
conjecture and observes that it is indeed trivial that $G(n)\to \infty$ for almost all $n$.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.parts.i : ∀ C : ℝ, {n : ℕ | C < G n}.HasDensity 1 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Can one prove an asymptotic formula for $\sum_{n\leq X}G(n)$?

Indeed $\sum_{n\leq X}G(n)\sim X\log X$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.parts.ii :
    (fun X : ℕ ↦ ∑ n ∈ Finset.Icc 1 X, G n) ~[atTop] fun X : ℕ ↦ (X : ℝ) * log X := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Erdős writes it is 'easy' to prove $\frac{1}{X}\sum_{n\leq X}G(n)\to \infty$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos673.lean#L914"]
theorem erdos_673.variants.average :
    Tendsto (fun X : ℕ ↦ (∑ n ∈ Finset.Icc 1 X, G n) / X) atTop atTop := by
  sorry

/-- Tao observed that, for any divisor $m\mid n$ with $m>1$,
$\frac{\tau(n/m)}{m} \leq G(n) \leq \tau(n)$. -/
@[category textbook, AMS 11]
theorem erdos_673.variants.tao (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card := by
  unfold G
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  have hpos : ∀ k, k < n.divisors.card → 0 < Nat.nth (· ∣ n) k := fun k hk => by
    have hdvd : Nat.nth (· ∣ n) k ∣ n := Nat.nth_mem_of_lt_card hf (by omega)
    exact Nat.pos_of_dvd_of_pos hdvd hn
  have hlt : ∀ i : Fin (n.divisors.card - 1),
      Nat.nth (· ∣ n) i < Nat.nth (· ∣ n) ((i : ℕ) + 1) := fun i =>
    Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) (by have := i.2; omega)
  have hnonneg : ∀ i : Fin (n.divisors.card - 1),
      0 ≤ (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1) := fun i => by positivity
  constructor
  · -- Each divisor `d` of `n / m` is followed by a divisor that is at most `m * d`, so its term
    -- of the sum is at least `1 / m`.
    have hK : 0 < n.divisors.card - 1 := by
      have h1 := Nat.count_strict_mono (p := (· ∣ n)) (one_dvd n)
        (lt_of_lt_of_le hm (Nat.le_of_dvd hn hmn))
      have h2 := Nat.count_lt_card hf (dvd_refl n)
      omega
    have key : ∀ d ∈ (n / m).divisors, d ∣ n ∧ Nat.count (· ∣ n) d < n.divisors.card - 1 ∧
        (1 : ℝ) / m ≤ (d : ℝ) / Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) := by
      intro d hd
      have hd' : d ∣ n / m := Nat.dvd_of_mem_divisors hd
      have hdn : d ∣ n := hd'.trans (Nat.div_dvd_of_dvd hmn)
      have hmd : m * d ∣ n := Nat.mul_dvd_of_dvd_div hmn hd'
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      have hc := Nat.count_strict_mono (p := (· ∣ n)) hdn (show d < m * d by nlinarith)
      have hc' := Nat.count_lt_card hf hmd
      have hnext : Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) ≤ m * d := by
        have := Nat.nth_le_nth_of_lt_card hf (Nat.succ_le_of_lt hc) hc'
        rwa [Nat.nth_count (p := (· ∣ n)) hmd] at this
      have hnext' : (Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) : ℝ) ≤ (m : ℝ) * d := by
        exact_mod_cast hnext
      have hnextpos : (0 : ℝ) < Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1) := by
        exact_mod_cast hpos _ (by omega)
      refine ⟨hdn, by omega, ?_⟩
      rw [div_le_div_iff₀ (by positivity) hnextpos]
      linarith [mul_comm (m : ℝ) d]
    obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → Fin (n.divisors.card - 1),
        ∀ d ∈ (n / m).divisors, (φ d : ℕ) = Nat.count (· ∣ n) d :=
      ⟨fun d => if h : Nat.count (· ∣ n) d < n.divisors.card - 1 then ⟨Nat.count (· ∣ n) d, h⟩
        else ⟨0, hK⟩, fun d hd => by simp only [dif_pos (key d hd).2.1]⟩
    have hinj : Set.InjOn φ ((n / m).divisors : Set ℕ) := fun d hd d' hd' h => by
      have h' := congrArg Fin.val h
      rw [hφ d hd, hφ d' hd'] at h'
      exact Nat.count_injective (key d hd).1 (key d' hd').1 h'
    calc ((n / m).divisors.card : ℝ) / m = ∑ d ∈ (n / m).divisors, (1 : ℝ) / m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ d ∈ (n / m).divisors,
            (Nat.nth (· ∣ n) (φ d) : ℝ) / Nat.nth (· ∣ n) ((φ d : ℕ) + 1) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [hφ d hd, Nat.nth_count (p := (· ∣ n)) (key d hd).1]
          exact (key d hd).2.2
      _ = ∑ i ∈ (n / m).divisors.image φ,
            (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1) :=
          (Finset.sum_image (f := fun i : Fin (n.divisors.card - 1) =>
            (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1)) hinj).symm
      _ ≤ ∑ i : Fin (n.divisors.card - 1),
            (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hnonneg i
  · -- Each term is at most `1`, and there are `τ(n) - 1` terms.
    have hterm : ∀ i : Fin (n.divisors.card - 1),
        (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1) ≤ 1 := fun i => by
      have h0 : (0 : ℝ) < Nat.nth (· ∣ n) ((i : ℕ) + 1) := by
        exact_mod_cast hpos _ (by have := i.2; omega)
      rw [div_le_one h0]
      exact_mod_cast (hlt i).le
    calc ∑ i : Fin (n.divisors.card - 1),
          (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) ((i : ℕ) + 1)
        ≤ ∑ _i : Fin (n.divisors.card - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
      _ = ((n.divisors.card - 1 : ℕ) : ℝ) := by simp
      _ ≤ n.divisors.card := by exact_mod_cast Nat.sub_le _ _

end Erdos673

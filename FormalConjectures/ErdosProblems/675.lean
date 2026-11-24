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
# Erdős Problem 675

*References:*
- [erdosproblems.com/675](https://www.erdosproblems.com/675)
- [Er79] Erdős, Paul, *Some unconventional problems in number theory*. Math. Mag. (1979), 67-70.
- [Ho26] Ho, B. S., *A squarefree lower bound for Erdős Problem 675*.
  [PDF](https://boonsuan.github.io/erdos675_squarefree.pdf) (2026).
-/

@[expose] public section

open Asymptotics Filter

namespace Erdos675

/--
`IsTranslation A n t` says that $t \geq 1$ and, for all $1 \leq a \leq n$, $a \in A$ if and
only if $a + t \in A$.
-/
def IsTranslation (A : Set ℕ) (n t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

/--
A set $A \subseteq \mathbb{N}$ has the translation property if, for every $n$, there is an
integer $t_n \geq 1$ such that, for all $1 \leq a \leq n$, $a \in A$ if and only if
$a + t_n \in A$.
-/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, IsTranslation A n t

/--
`minTranslation A n` is the least $t_n \geq 1$ such that, for all $1 \leq a \leq n$,
$a \in A$ if and only if $a + t_n \in A$. It is `0` if there is no such $t_n$.
-/
noncomputable def minTranslation (A : Set ℕ) (n : ℕ) : ℕ :=
  sInf {t : ℕ | IsTranslation A n t}

/-- `composedOf P` is the set of positive integers all of whose prime factors lie in `P`
(a version of `Nat.factoredNumbers` for an arbitrary set `P`). It contains $1$. -/
def composedOf (P : Set ℕ) : Set ℕ :=
  {m : ℕ | 0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P}

/-- The set $\{1\}$ does not have the translation property: for $n = 1$ it would need
$1 + t \in \{1\}$ for some $t \geq 1$. -/
@[category test, AMS 11]
theorem not_hasTranslationProperty_singleton_one : ¬ HasTranslationProperty {1} := by
  intro h
  obtain ⟨t, ht1, ht⟩ := h 1
  have h1 : 1 + t ∈ ({1} : Set ℕ) := (ht 1 le_rfl le_rfl).mp (Set.mem_singleton 1)
  rw [Set.mem_singleton_iff] at h1
  omega

/-- The numbers $1, 2, 3$ are squarefree, and $t = 4$ is the least $t \geq 1$ such that
$1 + t$, $2 + t$ and $3 + t$ are all squarefree. -/
@[category test, AMS 11]
theorem minTranslation_squarefree_three : minTranslation {m : ℕ | Squarefree m} 3 = 4 := by
  refine IsLeast.csInf_eq ⟨⟨by norm_num, fun a ha1 ha3 ↦ ?_⟩, fun t ⟨ht1, ht⟩ ↦ ?_⟩
  · interval_cases a <;> simp [Nat.squarefree_iff_nodup_primeFactorsList]
  · by_contra! h
    have := ht (4 - t) (by omega) (by omega)
    interval_cases t <;> simp [Nat.squarefree_iff_nodup_primeFactorsList] at this

/-- If `P` contains every prime, then `composedOf P` is the set of all positive integers. -/
@[category test, AMS 11]
theorem composedOf_primes : composedOf {p : ℕ | p.Prime} = {m : ℕ | 0 < m} := by
  ext m
  show (0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ {p : ℕ | p.Prime}) ↔ 0 < m
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hp _ ↦ hp⟩⟩

/--
A set $A \subseteq \mathbb{N}$ has the translation property if, for every $n$, there is an
integer $t_n \geq 1$ such that, for all $1 \leq a \leq n$, $a \in A$ if and only if
$a + t_n \in A$. Does the set of sums of two squares $\{x^2 + y^2 : x, y \in \mathbb{N}\}$
have the translation property?
-/
@[category research open, question, AMS 11]
theorem erdos_675.parts.i :
    HasTranslationProperty {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} := by
  sorry

/--
If we partition all primes into $P\sqcup Q$, such that each set contains $\gg x/\log x$ many
primes $\leq x$ for all large $x$, then can the set of integers only divisible by primes from
$P$ have the translation property?

We read "can" as: is there such a partition for which this set (which contains $1$) has the
translation property?
-/
@[category research open, question, AMS 11]
theorem erdos_675.parts.ii :
    ∃ P : Set ℕ, P ⊆ {p : ℕ | p.Prime} ∧
      (fun x : ℕ ↦ (x : ℝ) / Real.log x) =O[atTop] (fun x ↦ ((P ∩ Set.Iic x).ncard : ℝ)) ∧
      (fun x : ℕ ↦ (x : ℝ) / Real.log x) =O[atTop]
        (fun x ↦ ((({p : ℕ | p.Prime} \ P) ∩ Set.Iic x).ncard : ℝ)) ∧
      HasTranslationProperty (composedOf P) := by
  sorry

/--
If $A$ is the set of squarefree numbers then how fast does the minimal such $t_n$ grow? Is it
true that $t_n>\exp(n^c)$ for some constant $c>0$?

We ask for the inequality for all sufficiently large $n$, since $t_1 = 1$.

Ho [Ho26] proved that the answer is yes: for every fixed $0 < c < 25/72$, $t_n > \exp(n^c)$ for
all sufficiently large $n$ (Theorem 1.2 and Corollary 3.2); see also the
[forum discussion](https://www.erdosproblems.com/forum/thread/675#post-6002).
-/
@[category research solved, question, AMS 11]
theorem erdos_675.parts.iii :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ) ^ c) < (minTranslation {m : ℕ | Squarefree m} n : ℝ) := by
  sorry

/--
Elementary sieve theory implies that the set of squarefree numbers has the translation property
(as remarked on erdosproblems.com).
-/
@[category research solved, AMS 11]
theorem erdos_675.variants.squarefree : HasTranslationProperty {m : ℕ | Squarefree m} := by
  sorry

open scoped Classical in
/--
Let $B \subseteq \mathbb{N}$ be a set of pairwise coprime integers with
$$\sum_{b \in B,\ b < x} \frac{1}{b} = o(\log \log x).$$
Then $A = \{n : b \nmid n \text{ for all } b \in B\}$ has the translation property.
As remarked on erdosproblems.com, this follows from Brun's sieve, and Erdős did not know what
happens if the condition on the sum is weakened or dropped.
-/
@[category research solved, AMS 11]
theorem erdos_675.variants.brun (B : Set ℕ) (hB : B.Pairwise Nat.Coprime)
    (hsum : (fun x : ℕ ↦ ∑ b ∈ Finset.range x with b ∈ B, (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ ↦ Real.log (Real.log (x : ℝ))) :
    HasTranslationProperty {n : ℕ | ∀ b ∈ B, ¬ b ∣ n} := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
There are infinitely many $12$-shifts for the set $E$ of sums of two squares, that is,
infinitely many $t \geq 1$ with $a \in E \iff a + t \in E$ for all $1 \leq a \leq 12$.
In particular there are infinitely many $n$-shifts for every $n \leq 12$.

Let $u^2 = 2 W^2 + 1$ with $W \geq 1$. Put $x = 16 u^2 W^2 - 1$ and $t = x^2 - 1$. Then
$t + 1 = x^2$, $t + 2 = x^2 + 1^2$, $t + 5 = x^2 + 2^2$, $t + 10 = x^2 + 3^2$ and
$t + 9 = (x - 2)^2 + (8 u W)^2$ are sums of two squares, and so are $t + 8$ and $t + 4$, by
explicit identities that use the Pell equation. Since $32 \mid t$, the numbers $t + 3$, $t + 6$,
$t + 7$, $t + 11$, $t + 12$ are $3, 6, 7, 11, 12 \pmod{16}$, so they are not in $E$. The map
$(u, W) \mapsto (3 u + 4 W, 2 u + 3 W)$ preserves $u^2 - 2 W^2$, so the solution $(3, 2)$ gives
infinitely many solutions.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/c5e9a02f6c173f3bd5f39fac490440b44b5593d7/ErdosLean/Erdos675Twelve.lean"]
theorem erdos_675.variants.sumsOfTwoSquares_infinite_twelve_shifts :
    {t : ℕ | IsTranslation {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} 12 t}.Infinite := by
  sorry

end Erdos675

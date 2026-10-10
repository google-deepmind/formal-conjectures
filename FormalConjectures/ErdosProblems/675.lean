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
  sorry

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
@[category research open, AMS 11]
theorem erdos_675.parts.i :
    answer(sorry) ↔ HasTranslationProperty {m : ℕ | ∃ x y : ℕ, m = x ^ 2 + y ^ 2} := by
  sorry

/--
If we partition all primes into $P\sqcup Q$, such that each set contains $\gg x/\log x$ many
primes $\leq x$ for all large $x$, then can the set of integers only divisible by primes from
$P$ have the translation property?

We read "can" as: is there such a partition for which this set (which contains $1$) has the
translation property?
-/
@[category research open, AMS 11]
theorem erdos_675.parts.ii : answer(sorry) ↔
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
@[category research solved, AMS 11]
theorem erdos_675.parts.iii : answer(True) ↔
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

end Erdos675

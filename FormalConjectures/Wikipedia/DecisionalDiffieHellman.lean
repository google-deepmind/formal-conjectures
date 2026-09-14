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
# The decisional Diffie–Hellman assumption

The decisional Diffie–Hellman (DDH) assumption is a computational hardness assumption about a
cyclic group $G = \langle g \rangle$ of prime order $q$: given $g^a$ and $g^b$ for uniformly
random $a, b \in \mathbb{Z}_q$, the element $g^{ab}$ is computationally indistinguishable from a
uniformly random element $g^c$ of $G$. That is, for every probabilistic polynomial-time
algorithm $\mathcal{A}$ the distinguishing advantage
$$\bigl|\Pr[\mathcal{A}(g^a, g^b, g^{ab}) = 1] - \Pr[\mathcal{A}(g^a, g^b, g^{c}) = 1]\bigr|$$
is negligible in the security parameter $\log q$.

## Group families

The assumption is a statement about a family of groups, so this file first defines the
distinguishing advantage for an arbitrary group with a chosen encoding of challenges, and then
states the assumption for concrete families of subgroups of $\mathbb{Z}_p^\times$:

* `ddh_safe_prime`: the subgroup of quadratic residues of $\mathbb{Z}_p^\times$ for a safe
  prime $p = 2q + 1$, i.e. its unique subgroup of prime order $q$;
* `ddh_schnorr`: more generally, a subgroup of prime order $q$ of $\mathbb{Z}_p^\times$
  (a Schnorr group), where the bit length of $p$ is bounded by a fixed power of that of $q$.

The assumption fails in $\mathbb{Z}_p^\times$ itself, since the Legendre symbol of $g^{ab}$ is
determined by those of $g^a$ and $g^b$; this is recorded in `not_ddh_units_zmod`. It also
fails in any group with an efficiently computable bilinear pairing, so a statement for
elliptic curve groups requires an embedding degree condition and is left for future work.

## Computational model

Following `FormalConjecturesForMathlib/Computability/Complexity.lean`, an efficient algorithm
is a function that is computable in polynomial time by a deterministic Turing machine
(`ComplexityTheory.IsPolyTime`, built on Mathlib's `Turing.TM2ComputableInPolyTime`), with
inputs and outputs encoded by the canonical `BitstringEncoding`. A *probabilistic*
polynomial-time distinguisher is such a function that receives, besides the challenge
$(g^a, g^b, z)$ together with the public parameters of the group, a uniformly random tape of
polynomially many bits. Probabilities are taken over the uniform distribution on the finite set
of exponents and random tapes, and "negligible" means eventually below every inverse
polynomial in the security parameter. The statements ask for the advantage to be small on
*every* instance of the family at a given security level, which is the reading of "DDH holds
in this family of groups" and implies the variants where the instance is generated at random.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Decisional_Diffie%E2%80%93Hellman_assumption)
* D. Boneh, [*The Decision Diffie-Hellman problem*](https://doi.org/10.1007/BFb0054851),
  Algorithmic Number Theory (ANTS-III), LNCS 1423 (1998), 48–63.
* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press (2014),
  Chapter 8.
-/

open ComplexityTheory Filter

namespace DecisionalDiffieHellman

/- ## Distinguishers and their advantage -/

/-- The probability that `f` is `true` at a uniformly random element of the finite type `ι`. -/
noncomputable def uniformProb (ι : Type*) [Fintype ι] (f : ι → Bool) : ℝ :=
  (Finset.univ.filter (f · = true)).card / Fintype.card ι

/-- A probabilistic polynomial-time distinguisher for challenges of type `α`: a function `run`
from a challenge and a random tape to a verdict, computable in polynomial time by a
deterministic Turing machine (so its running time is polynomial in the length of the challenge
and of the tape), together with a polynomial `randomBits` giving the number of random bits used
at each security level. -/
structure PPTDistinguisher (α : Type) [BitstringEncoding α] where
  /-- The distinguisher, as a function of the challenge and the random tape. -/
  run : α × List Bool → Bool
  /-- `run` is computable in polynomial time by a deterministic Turing machine. -/
  polyTime : IsPolyTime run
  /-- The number of random bits used, as a polynomial in the security parameter. -/
  randomBits : Polynomial ℕ

/-- The DDH advantage of the distinguisher `D` against the cyclic group of order `q` generated
by `g : G`, at security parameter `n` (which fixes the number `D.randomBits.eval n` of random
bits), where `challenge x y z : α` is the challenge handed to `D` for the triple `(x, y, z)`:
the absolute difference between the probability that `D` accepts a real Diffie–Hellman triple
$(g^a, g^b, g^{ab})$ and the probability that it accepts a random triple $(g^a, g^b, g^c)$,
for $a, b, c$ uniform in $\{0, \dots, q - 1\}$ and a uniform random tape. -/
noncomputable def advantage {α : Type} [BitstringEncoding α] {G : Type*} [Group G]
    (D : PPTDistinguisher α) (challenge : G → G → G → α) (g : G) (q n : ℕ) : ℝ :=
  |uniformProb (Fin q × Fin q × (Fin (D.randomBits.eval n) → Bool))
      (fun ⟨a, b, r⟩ ↦
        D.run (challenge (g ^ (a : ℕ)) (g ^ (b : ℕ)) (g ^ ((a : ℕ) * (b : ℕ))), List.ofFn r)) -
    uniformProb (Fin q × Fin q × Fin q × (Fin (D.randomBits.eval n) → Bool))
      (fun ⟨a, b, c, r⟩ ↦
        D.run (challenge (g ^ (a : ℕ)) (g ^ (b : ℕ)) (g ^ (c : ℕ)), List.ofFn r))|

/- ## Subgroups of `(ZMod p)ˣ` -/

/-- A DDH challenge in `(ZMod p)ˣ`: the tuple `(p, g, x, y, z)` of the modulus, the generator
and the three group elements, all as natural numbers (group elements as their least
non-negative residues). It is handed to a distinguisher through the canonical
`BitstringEncoding` of tuples of natural numbers. -/
abbrev Challenge : Type := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The challenge `(p, g, x, y, z)` for group elements `g x y z : (ZMod p)ˣ`. -/
def challenge (p : ℕ) (g x y z : (ZMod p)ˣ) : Challenge :=
  (p, (g : ZMod p).val, (x : ZMod p).val, (y : ZMod p).val, (z : ZMod p).val)

/-- `(p, q, g)` is a DDH instance in the family of quadratic-residue subgroups of safe primes:
$p = 2q + 1$ with $p$ and $q$ prime, and $g \in \mathbb{Z}_p^\times$ has order $q$, so that
$g$ generates the subgroup of quadratic residues. -/
def IsSafePrimeInstance (p q : ℕ) (g : (ZMod p)ˣ) : Prop :=
  p.Prime ∧ q.Prime ∧ p = 2 * q + 1 ∧ orderOf g = q

/-- **The decisional Diffie–Hellman assumption** for the subgroups of quadratic residues of
$\mathbb{Z}_p^\times$ with $p = 2q + 1$ a safe prime, with security parameter the bit length
$n = \operatorname{size} q$ of $q$: for every probabilistic polynomial-time distinguisher `D`
and every $c \in \mathbb{N}$, for all sufficiently large $n$, the DDH advantage of `D` is at
most $n^{-c}$ on every instance at security level $n$. -/
@[category research open, AMS 11 68 94]
theorem ddh_safe_prime (D : PPTDistinguisher Challenge) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (p q : ℕ) (g : (ZMod p)ˣ), IsSafePrimeInstance p q g →
      Nat.size q = n → advantage D (challenge p g) g q n ≤ 1 / (n : ℝ) ^ c := by
  sorry

/-- `(p, q, g)` is a DDH instance in the family of Schnorr groups with parameters polynomially
related with exponent `d`: $p$ and $q$ are primes with $q \mid p - 1$, the element
$g \in \mathbb{Z}_p^\times$ has order $q$, and the bit length of $p$ is at most the $d$-th
power of that of $q$. Safe primes are the case $p = 2q + 1$, which satisfies the bound for
$d = 2$. -/
def IsSchnorrInstance (d p q : ℕ) (g : (ZMod p)ˣ) : Prop :=
  p.Prime ∧ q.Prime ∧ q ∣ p - 1 ∧ orderOf g = q ∧ Nat.size p ≤ Nat.size q ^ d

/-- **The decisional Diffie–Hellman assumption** for Schnorr groups: for every $d$, every
probabilistic polynomial-time distinguisher `D` and every $c \in \mathbb{N}$, for all
sufficiently large $n$, the DDH advantage of `D` is at most $n^{-c}$ on every subgroup of
prime order $q$ of $\mathbb{Z}_p^\times$ with $\operatorname{size} q = n$ and
$\operatorname{size} p \le n^d$. -/
@[category research open, AMS 11 68 94]
theorem ddh_schnorr (d : ℕ) (D : PPTDistinguisher Challenge) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (p q : ℕ) (g : (ZMod p)ˣ), IsSchnorrInstance d p q g →
      Nat.size q = n → advantage D (challenge p g) g q n ≤ 1 / (n : ℝ) ^ c := by
  sorry

/-- The DDH assumption fails in the full group $\mathbb{Z}_p^\times$: for a generator $g$ the
Legendre symbol of $g^{ab}$ is $-1$ exactly when those of $g^a$ and $g^b$ are both $-1$, while
the Legendre symbol of a uniformly random $g^c$ is $\pm 1$ with probability $1/2$ each. Since
Legendre symbols are computable in polynomial time, there is a distinguisher with advantage
$1/2$ on every instance. -/
@[category textbook, AMS 11 68 94]
theorem not_ddh_units_zmod :
    ∃ D : PPTDistinguisher Challenge, ∀ (p : ℕ) (g : (ZMod p)ˣ), p.Prime → 3 ≤ p →
      orderOf g = p - 1 →
      1 / 2 ≤ advantage D (challenge p g) g (p - 1) (Nat.size (p - 1)) := by
  sorry

/- ## Basic API -/

/-- A uniform probability lies in $[0, 1]$. -/
@[category API, AMS 60]
theorem uniformProb_mem_Icc (ι : Type*) [Fintype ι] (f : ι → Bool) :
    uniformProb ι f ∈ Set.Icc (0 : ℝ) 1 := by
  unfold uniformProb
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast (Finset.card_filter_le _ _).trans Finset.card_univ.le

/-- The DDH advantage is at most $1$. -/
@[category API, AMS 11 68 94]
theorem advantage_le_one {α : Type} [BitstringEncoding α] {G : Type*} [Group G]
    (D : PPTDistinguisher α) (challenge : G → G → G → α) (g : G) (q n : ℕ) :
    advantage D challenge g q n ≤ 1 := by
  unfold advantage
  have key : ∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → |x - y| ≤ 1 := fun x y hx hy ↦
    abs_sub_le_iff.2 ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
  exact key _ _ (uniformProb_mem_Icc _ _) (uniformProb_mem_Icc _ _)

/-- A distinguisher that always accepts has zero advantage. -/
@[category test, AMS 11 68 94]
theorem advantage_eq_zero_of_forall_run {α : Type} [BitstringEncoding α] {G : Type*} [Group G]
    (D : PPTDistinguisher α) (h : ∀ x, D.run x = true) (challenge : G → G → G → α) (g : G)
    (q n : ℕ) : advantage D challenge g q n = 0 := by
  simp [advantage, uniformProb, h]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    rw [div_self (by positivity), div_self (by positivity), sub_self]

end DecisionalDiffieHellman

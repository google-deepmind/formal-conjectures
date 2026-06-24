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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1212

*References:*
- [erdosproblems.com/1212](https://www.erdosproblems.com/1212)
- [Er80] Erdős, P., _Some notes on problems and results in number theory_ (1980), p. 114.

This file also records machine-checked cores of verified partial results (2026):
a composite-anchor sufficient reduction and an impossibility theorem for periodic
certificates; see the corresponding lemmas below.
-/

open Filter

namespace Erdos1212

/-- A vertex of the strengthened problem: a visible lattice point with both coordinates
exceeding 1 and at least one coordinate composite. -/
def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧ (¬ p.1.Prime ∨ ¬ p.2.Prime)

/-- Sanity check for `Valid`: the vertex $(4, 3)$ is valid — both coordinates exceed $1$,
they are coprime, and $4$ is composite. -/
@[category test, AMS 11]
theorem valid_four_three : Valid (4, 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Two lattice points are adjacent iff they differ by exactly 1 in exactly one coordinate. -/
def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

/--
Let $G$ be the graph with vertex set those pairs $(x,y)\in \mathbb{N}^2$ with
$\mathrm{gcd}(x,y)=1$, in which we join two vertices if the differ in only one coordinate, and
there by $\pm 1$.

Is there a path going to infinity on $G$, say $P$, such that for all $(x,y)\in P$ both
$\min(x,y)>1$ and at least one of $x$ or $y$ is composite?

The weaker version (only $\min(x,y) > 1$) was solved by C. Stewart via the prime-pair path
$(p_k, p_{k+1}) \to (p_{k+1}, p_{k+2})$, as recounted in [Er80]; the compositeness condition
forbids those anchors and the question is open.
-/
@[category research open, AMS 11]
theorem erdos_1212 :
    answer(sorry) ↔ ∃ f : ℕ → ℕ × ℕ, Function.Injective f ∧ (∀ n, Adj (f n) (f (n + 1))) ∧
      (∀ n, Valid (f n)) ∧
      Tendsto (fun n => (f n).1 + (f n).2) atTop atTop := by
  sorry

/- ### Verified partial results (2026): machine-checked cores -/

/-- Core of the composite-anchor reduction: vertical-leg vertices $(a, s)$ for
$b \le s \le c$ are valid vertices of the strengthened problem, given the anchor $a$ is
composite and coprime to the whole leg. -/
@[category API, AMS 11]
theorem vertical_leg_valid {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b)
    (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    ∀ s, b ≤ s → s ≤ c → Valid (a, s) := by
  intro s hs1 hs2
  have ha2 := ha.1
  exact ⟨by omega, by omega, hV s hs1 hs2, Or.inl ha.2⟩

/-- Core of the composite-anchor reduction: horizontal-leg vertices $(s, c)$ for
$a \le s \le b$ are valid, given the anchor $c$ is composite and coprime to the whole leg. -/
@[category API, AMS 11]
theorem horizontal_leg_valid {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a)
    (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    ∀ s, a ≤ s → s ≤ b → Valid (s, c) := by
  intro s hs1 hs2
  have hc2 := hc.1
  exact ⟨by omega, by omega, hH s hs1 hs2, Or.inr hc.2⟩

/-- Roughness criterion (sufficiency for the anchor conditions): if $a < s$ for all $s$ in
the leg and the leg stays below $a + P^-(a)$, then $a$ is coprime to the whole leg. Stated
via divisibility: no prime factor of $a$ divides any $s$ with $a < s < a + p$ for all
prime factors $p$ of $a$. -/
@[category API, AMS 11]
theorem anchor_coprime_of_short_leg {a s : ℕ} (hs : a < s)
    (h : ∀ p, p.Prime → p ∣ a → s < a + p) : Nat.gcd a s = 1 := by
  by_contra hg
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd a s) (by
    intro h1
    exact hg h1)
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a s)
  have hps : p ∣ s := hpd.trans (Nat.gcd_dvd_right a s)
  have hlt : s < a + p := h p hp hpa
  -- s is a multiple of p strictly between a (a multiple of p) and a + p: impossible
  obtain ⟨k, hk⟩ := hpa
  obtain ⟨l, hl⟩ := hps
  have hp0 : 0 < p := hp.pos
  have hkl : k < l := by
    have : p * k < p * l := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have : p * (k + 1) ≤ p * l := Nat.mul_le_mul_left p hkl
  have : a + p ≤ s := by
    have hpk : p * (k + 1) = a + p := by rw [hk]; ring
    omega
  omega

/-- Isolation lemma, right neighbour (core of the no-periodic-certificate theorem): if every
prime in $P$ divides $x$ and none divides $y$, then no prime of $P$ divides either
coordinate of $(x+1, y)$. -/
@[category API, AMS 11]
theorem right_neighbor_witness_free {P : Finset ℕ} {x y : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hx : ∀ p ∈ P, p ∣ x) (hy : ∀ p ∈ P, ¬ p ∣ y) :
    ∀ p ∈ P, ¬ p ∣ (x + 1) ∧ ¬ p ∣ y := by
  intro p hp
  refine ⟨fun hdvd => ?_, hy p hp⟩
  have h1 : p ∣ 1 := by
    have h := Nat.dvd_sub hdvd (hx p hp)
    simpa using h
  have := (hP p hp).one_lt
  have := Nat.dvd_one.mp h1
  omega

/-- Isolation lemma, left neighbour. -/
@[category API, AMS 11]
theorem left_neighbor_witness_free {P : Finset ℕ} {x y : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hx1 : 1 ≤ x) (hx : ∀ p ∈ P, p ∣ x) (hy : ∀ p ∈ P, ¬ p ∣ y) :
    ∀ p ∈ P, ¬ p ∣ (x - 1) ∧ ¬ p ∣ y := by
  intro p hp
  refine ⟨fun hdvd => ?_, hy p hp⟩
  have h1 : p ∣ 1 := by
    have h := Nat.dvd_sub (hx p hp) hdvd
    have hx_sub : x - (x - 1) = 1 := by omega
    rwa [hx_sub] at h
  have := (hP p hp).one_lt
  have := Nat.dvd_one.mp h1
  omega

/-- Isolation lemma, vertical neighbours: both coordinates even. -/
@[category API, AMS 11]
theorem vertical_neighbor_both_even {x y : ℕ} (h2x : 2 ∣ x) (h2y : ¬ 2 ∣ y) :
    (2 ∣ x ∧ 2 ∣ (y + 1)) ∧ (1 ≤ y → 2 ∣ x ∧ 2 ∣ (y - 1)) := by
  refine ⟨⟨h2x, by omega⟩, fun hy1 => ⟨h2x, by omega⟩⟩

end Erdos1212

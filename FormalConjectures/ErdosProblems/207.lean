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
# Erdős Problem 207

*Reference:* [erdosproblems.com/207](https://www.erdosproblems.com/207)

[KSSS22b] Kwan, M., Sah, A., Sawhney, M., and Simkin, M.,
_High-girth Steiner triple systems_. [arXiv:2201.04554](https://arxiv.org/abs/2201.04554) (2022).
-/

@[expose] public section

open Finset

section

namespace Erdos207

variable {V : Type*} [DecidableEq V]

/-- The *girth condition* of Erdős Problem 207 for the parameter `g`: for every `2 ≤ j ≤ g`,
any collection of `j` (distinct) edges of `H` spans at least `j + 3` vertices. -/
def GirthCondition (H : Finset (Finset V)) (g : ℕ) : Prop :=
  ∀ S ⊆ H, 2 ≤ S.card → S.card ≤ g → S.card + 3 ≤ (S.biUnion id).card

/-- The proposition stated by Erdős Problem 207. -/
def Statement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ᶠ n in Filter.atTop, (n % 6 = 1 ∨ n % 6 = 3) →
    ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g

/--
For any $g\geq 2$, if $n$ is sufficiently large and $n\equiv 1,3\pmod{6}$ then there exists a
3-uniform hypergraph on $n$ vertices such that
* every pair of vertices is contained in exactly one edge (i.e. the graph is a Steiner triple
  system) and
* for any $2\leq j\leq g$ any collection of $j$ edges contains at least $j+3$ vertices.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos207.lean#L400"]
theorem erdos_207 : Statement := by
  sorry

end Erdos207

end

namespace Erdos207

variable {V : Type*} [DecidableEq V]

/-- Every Steiner triple system satisfies the girth condition of Erdős Problem 207 for `g = 3`:
any two edges span at least `5` vertices and any three edges span at least `6` vertices. -/
@[category API, AMS 5]
theorem girthCondition_three {H : Finset (Finset V)}
    (hH : IsSteinerTripleSystem H) : GirthCondition H 3 := by
  intro S hS h2 h3
  have hc : ∀ e ∈ S, e.card = 3 := fun e he => hH.card_triple e (hS he)
  have hi : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (e ∩ f).card ≤ 1 := fun e he f hf hef =>
    hH.card_inter_le_one (hS he) (hS hf) hef
  have two : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → 5 ≤ (e ∪ f).card := fun e he f hf hef => by
    have := Finset.card_union_add_card_inter e f
    have := hi e he f hf hef
    rw [hc e he, hc f hf] at *
    omega
  interval_cases hSc : S.card
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hSc
    simp only [Finset.biUnion_insert, id, Finset.singleton_biUnion]
    exact two a (by simp) b (by simp) hab
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hSc
    simp only [Finset.biUnion_insert, id, Finset.singleton_biUnion]
    have hab' := two a (by simp) b (by simp) hab
    have h1 := Finset.card_union_add_card_inter (a ∪ b) c
    have h2 : ((a ∪ b) ∩ c).card ≤ (a ∩ c).card + (b ∩ c).card := by
      rw [Finset.union_inter_distrib_right]; exact Finset.card_union_le _ _
    have := hi a (by simp) c (by simp) hac
    have := hi b (by simp) c (by simp) hbc
    have := hc c (by simp)
    rw [← Finset.union_assoc]
    omega

/-- The girth condition is monotone in `g`. -/
@[category API, AMS 5]
theorem GirthCondition.mono {H : Finset (Finset V)} {g g' : ℕ} (h : GirthCondition H g)
    (hg : g' ≤ g) : GirthCondition H g' :=
  fun S hS h2 h3 => h S hS h2 (h3.trans hg)

end Erdos207

/- Basic cases and the Fano plane. -/

section

namespace Erdos207

/-- The congruence condition of Erdős Problem 207 is necessary: if some Steiner triple system on
`n ≥ 1` points satisfies the girth condition (for any `g`), then `n ≡ 1, 3 (mod 6)`. -/
@[category API, AMS 5]
theorem mod_six_of_exists {n g : ℕ} (hn : 1 ≤ n)
    (h : ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g) :
    n % 6 = 1 ∨ n % 6 = 3 := by
  obtain ⟨H, hH, -⟩ := h
  exact (exists_isSteinerTripleSystem_iff hn).1 ⟨H, hH⟩

/-- Erdős Problem 207 for `g ≤ 3` holds for **every** `n ≡ 1, 3 (mod 6)`. -/
@[category API, AMS 5]
theorem exists_of_le_three {g n : ℕ} (hg : g ≤ 3) (hn : n % 6 = 1 ∨ n % 6 = 3) :
    ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g := by
  obtain ⟨H, hH⟩ := (exists_isSteinerTripleSystem_iff (by omega)).2 hn
  exact ⟨H, hH, (girthCondition_three hH).mono hg⟩

/-- The statement of Erdős Problem 207 restricted to `g ∈ {2, 3}`. -/
@[category test, AMS 5]
theorem statement_of_le_three : ∀ g : ℕ, 2 ≤ g → g ≤ 3 → ∀ᶠ n in Filter.atTop,
    (n % 6 = 1 ∨ n % 6 = 3) →
      ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g :=
  fun _ _ hg => Filter.Eventually.of_forall fun _ hn => exists_of_le_three hg hn

/-- The Fano plane, as a Steiner triple system on `Fin 7` (lines `{i, i + 1, i + 3}`). -/
def fano : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2}}

/-- The Fano plane is a Steiner triple system. -/
@[category test, AMS 5]
theorem isSteinerTripleSystem_fano : IsSteinerTripleSystem fano := by
  refine isSteinerTripleSystem_iff.2 ⟨by simp [fano], fun x y hxy => ?_⟩
  have h : ∀ x y : Fin 7, x ≠ y → (fano.filter fun e => x ∈ e ∧ y ∈ e).card = 1 := by
    unfold fano; decide
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 (h x y hxy)
  have hmem : ∀ f, f ∈ fano ∧ x ∈ f ∧ y ∈ f ↔ f = e := fun f => by
    rw [← Finset.mem_singleton, ← he, Finset.mem_filter]
  exact ⟨e, (hmem e).2 rfl, fun f hf => (hmem f).1 hf⟩

/-- The girth condition for `g = 4` is a genuine restriction: the Fano plane contains a Pasch
configuration (four lines on six points), so it violates the condition for `g = 4`. -/
@[category test, AMS 5]
theorem not_girthCondition_four_fano : ¬ GirthCondition fano 4 := by
  intro h
  have := h {{1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {5, 6, 1}} (by decide) (by decide) (by decide)
  revert this
  decide

end Erdos207

end

namespace Erdos207

/-- The congruence condition $n \equiv 1, 3 \pmod 6$ is necessary. -/
@[category textbook, AMS 5]
theorem erdos_207.variants.mod_six_necessary {n g : ℕ} (hn : 1 ≤ n)
    (h : ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g) :
    n % 6 = 1 ∨ n % 6 = 3 :=
  mod_six_of_exists hn h

/-- For $g \le 3$ the statement holds for every $n \equiv 1, 3 \pmod 6$. -/
@[category textbook, AMS 5]
theorem erdos_207.variants.le_three {g n : ℕ} (hg : g ≤ 3) (hn : n % 6 = 1 ∨ n % 6 = 3) :
    ∃ H : Finset (Finset (Fin n)), IsSteinerTripleSystem H ∧ GirthCondition H g :=
  exists_of_le_three hg hn

end Erdos207

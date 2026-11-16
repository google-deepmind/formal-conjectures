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
# Erdős Problem 902

*References:*
- [erdosproblems.com/902](https://www.erdosproblems.com/902)
- [Er63c] Erdős, P., *On a problem in graph theory*. Math. Gaz. 47 (1963), 220-223.
  [PDF](https://www.renyi.hu/~p_erdos/1963-08.pdf)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59-79.
- [SzSz65] Szekeres, E. and Szekeres, G., *On a problem of Schütte and Erdős*. Math. Gaz. 49
  (1965), 290-293.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos902

/-- `HasPropertyS G n` is Schütte's property $S_n$ [Er63c]: every set `E` of `n` vertices is
dominated by a vertex outside it, that is, some vertex `x ∉ E` has an edge to every vertex of
`E`. -/
def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

/-- $f(n)$: the least number of vertices of a tournament with property $S_n$.

A tournament with fewer than $n$ vertices has no set of $n$ vertices, so it has property $S_n$
vacuously; the condition `n ≤ m` excludes this case. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}

/-- The cyclic tournament on three vertices, `a → a + 1`, has property $S_1$, so
$f(1) \leq 3$. -/
@[category test, AMS 5]
theorem f_one_le : f 1 ≤ 3 := by
  refine Nat.sInf_le ⟨by norm_num, ⟨fun a b => b = a + 1⟩, ⟨by decide, by decide⟩, ?_⟩
  intro E hE
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hE
  have key : ∀ a : Fin 3, a + 2 ≠ a ∧ a = a + 2 + 1 := by decide
  refine ⟨a + 2, by simp [(key a).1], fun e he => ?_⟩
  rw [Finset.mem_singleton.1 he]
  exact (key a).2

/-- Erdős's tournament on seven vertices [Er63c], with `a → a + 1, a + 2, a + 4` modulo $7$,
has property $S_2$, so $f(2) \leq 7$. -/
@[category test, AMS 5]
theorem f_two_le : f 2 ≤ 7 := by
  refine Nat.sInf_le ⟨by norm_num, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
    ⟨by decide, by decide⟩, ?_⟩
  intro E hE
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
  have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
      a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
    decide
  obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
  refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
  rcases Finset.mem_insert.1 he with rfl | he
  · exact ha
  · rw [Finset.mem_singleton.1 he]
    exact hb

def erdos_902.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be minimal such that there is a tournament (a complete directed graph) on $f(n)$
vertices such that every set of $n$ vertices is dominated by at least one other vertex.
Estimate $f(n)$.
-/
@[category research open, question value, AMS 5]
theorem erdos_902 : (fun n ↦ (f n : ℝ)) =Θ[atTop] erdos_902.answer := by
  sorry

/--
It is easy to check that $f(1)=3$ and $f(2)=7$.

This is the statement for $f(1)$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.f_one : f 1 = 3 := by
  refine le_antisymm f_one_le (le_csInf ⟨3, ?_⟩ ?_)
  · refine ⟨by norm_num, ⟨fun a b => b = a + 1⟩, ⟨by decide, by decide⟩, ?_⟩
    intro E hE
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hE
    have key : ∀ a : Fin 3, a + 2 ≠ a ∧ a = a + 2 + 1 := by decide
    refine ⟨a + 2, by simp [(key a).1], fun e he => ?_⟩
    rw [Finset.mem_singleton.1 he]
    exact (key a).2
  · rintro m ⟨hm, G, hG, hS⟩
    by_contra! hm3
    interval_cases m
    · obtain ⟨x, hx, -⟩ := hS {0} rfl
      exact hx (by simp [Subsingleton.elim x 0])
    · have h01 := hG.2 0 1 (by decide)
      by_cases h : G.Adj 0 1
      · obtain ⟨x, hx, hx0⟩ := hS {0} rfl
        have hx1 : x = 1 := by fin_cases x <;> simp_all
        subst hx1
        exact h01.1 h (hx0 0 (by simp))
      · obtain ⟨x, hx, hx1⟩ := hS {1} rfl
        have hx0 : x = 0 := by fin_cases x <;> simp_all
        subst hx0
        exact h (hx1 1 (by simp))

/--
It is easy to check that $f(1)=3$ and $f(2)=7$.

This is the statement for $f(2)$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.f_two : f 2 = 7 := by
  sorry

/--
Erdős [Er63c] proved
$$2^{n+1}-1 \leq f(n) \ll n^22^n.$$

This is the lower bound.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.erdos_lower (n : ℕ) : 2 ^ (n + 1) - 1 ≤ f n := by
  sorry

/--
Erdős [Er63c] proved
$$2^{n+1}-1 \leq f(n) \ll n^22^n.$$

This is the upper bound, in the form proved in [Er63c, (2)]:
$\limsup_n f(n)2^{-n}n^{-2} \leq \log 2$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.erdos_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (Real.log 2 + ε) * n ^ 2 * 2 ^ n := by
  sorry

/--
Szekeres and Szekeres [SzSz65] proved that $f(3)=19$ and
$$n2^n \ll f(n).$$

This is the statement for $f(3)$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.szekeres_f_three : f 3 = 19 := by
  sorry

/--
Szekeres and Szekeres [SzSz65] proved that $f(3)=19$ and
$$n2^n \ll f(n).$$

This is the lower bound.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.szekeres_lower :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * n * 2 ^ n ≤ (f n : ℝ) := by
  sorry

end Erdos902

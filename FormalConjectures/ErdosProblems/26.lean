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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 26

*References:*
- [erdosproblems.com/26](https://www.erdosproblems.com/26)
- [Te19](https://arxiv.org/pdf/1908.00488) G. Tenenbaum,
  _Some of Erdős' unconventional problems in number theory, thirty-four years later_,
  arXiv:1908.00488 [math.NT] (2019)
-/

namespace Erdos26

/-- A sequence of naturals $(a_i)$ is _thick_ if their sum of reciprocals diverges:
$$
  \sum_i \frac{1}{a_i} = \infty
$$-/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

@[category test, AMS 11]
theorem not_isThick_of_finite {ι : Type*} [Finite ι] (A : ι → ℕ) : ¬IsThick A := by
  simpa [IsThick] using .of_finite

/-- The set of multiples of a sequence $(a_i)$ is $\{ na_i | n \in \mathbb{N}, i\}$. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

@[category test, AMS 11]
theorem multiplesOf_eq_univ {ι : Type*} (A : ι → ℕ) (h : 1 ∈ Set.range A) :
    MultiplesOf A = Set.univ := by
  obtain ⟨i, hi⟩ := h
  exact top_unique fun n hn ↦ ⟨(n, i), by simp [hi]⟩

/-- A sequence of naturals $(a_i)$ is _Behrend_ if almost all integers are a multiple of
some $a_i$. In other words, if the set of multples has natural density $1$. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := (MultiplesOf A).HasDensity 1

/-- A sequence of naturals $(a_i)$ is _weakly Behrend_ with respect to $\varepsilon \in \mathbb{R}$
if at least $1 - \varepsilon$ density of all numbers are a multiple of $A$. -/
def IsWeaklyBehrend {ι : Type*} (A : ι → ℕ) (ε : ℝ) : Prop :=
  ∀ d > (0 : ℝ), (MultiplesOf A).HasDensity d → 1 - ε ≤ d

@[category test, AMS 11]
theorem isBehrend_of_contains_one {ι : Type*} (A : ι → ℕ) (h : 1 ∈ Set.range A) :
    IsBehrend A := by
  rw [IsBehrend, Set.HasDensity]
  exact tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn ↦ by
    field_simp [multiplesOf_eq_univ A h, Set.partialDensity]

@[category test, AMS 11]
theorem not_isBehrend_finite {ι : Type*} [Finite ι] [Preorder ι] (A : ι → ℕ) (h : StrictMono A)
    (h : 1 ∉ Set.range A) : ¬IsBehrend A := by
  sorry

@[category test, AMS 11]
theorem isWeaklyBehrend_of_ge_one {ι : Type*} (A : ι → ℕ) {ε : ℝ} (hε : 1 ≤ ε) :
    IsWeaklyBehrend A ε := fun _ h _ => (sub_nonpos.2 hε).trans h.le

/--
Let $A\subset\mathbb{N}$ be infinite such that $\sum_{a \in A} \frac{1}{a} = \infty$. Must
there exist some $k\geq 1$ such that almost all integers have a divisor of the form $a+k$
for some $a\in A$?
-/
@[category research open, AMS 11]
theorem erdos_26 (A : ℕ → ℕ) (hA : StrictMono A) (h : IsThick A) :
    (∃ k, IsBehrend (A · + k)) ↔ answer(True) := by
  sorry

/--
If we allow for $\sum_{a\in A} \frac{1}{a} < \infty$ then Rusza has found a counter-example.
-/
@[category research solved, AMS 11]
theorem erdos_26.variants.rusza : ∃ A : ℕ → ℕ,
    StrictMono A ∧ ¬IsThick A ∧ ∀ k, ¬IsBehrend (A · + k) := by
  sorry

/--
Tenenbaum asked the weaker variant (still open) where for every $\epsilon>0$ there is
some $k=k(\epsilon)$ such that at least $1-\epsilon$ density of all integers have a
divisor of the form $a+k$ for some $a\in A$.
-/
@[category research open, AMS 11]
theorem erdos_26.variants.tenenbaum (A : ℕ → ℕ) (hA : StrictMono A) (h : IsThick A) :
    (∀ ε > (0 : ℝ), ∃ k, IsWeaklyBehrend (A · + k) ε) ↔ answer(sorry) := by
  sorry

end Erdos26

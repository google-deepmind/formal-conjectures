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
# Erdős Problem 1025

*References:*
- [erdosproblems.com/1025](https://www.erdosproblems.com/1025)
- [CFS16] Conlon, David and Fox, Jacob and Sudakov, Benny, *Short proofs of some extremal results II*.
  J. Combin. Theory Ser. B (2016), 173--196.
- [ErHa58] Erdős, P. and Hajnal, A., *On the structure of set mappings*.
  Acta Math. Acad. Sci. Hungar. (1958), 111-133.
- [Sp72] Spencer, Joel, *Turán's theorem for k-graphs*.
  Discrete Math. (1972), 183--186.
-/

open Filter Asymptotics

namespace Erdos1025

/--
A function from unordered pairs of an `n`-element set to the same set, sending every pair
to a point outside the pair.

This is the Erdős–Hajnal set mapping of type $(2,1)$: the source writes $f(x,y)$ for a
function on pairs, which we take as symmetric and defined on distinct arguments.
-/
def IsPairMapping {n : ℕ} (f : Fin n → Fin n → Fin n) : Prop :=
  (∀ x y, f x y = f y x) ∧ ∀ ⦃x y⦄, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/--
`X` is independent for `f` if $f(x,y)\notin X$ whenever $x,y\in X$ are distinct.
-/
def IsIndependent {n : ℕ} (f : Fin n → Fin n → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y ∉ X

/--
The size of a largest independent set for `f`. The empty set is always independent, so this
is well-defined.
-/
noncomputable def independenceNumber {n : ℕ} (f : Fin n → Fin n → Fin n) : ℕ :=
  sSup {m | ∃ X : Finset (Fin n), IsIndependent f X ∧ X.card = m}

/--
`g n` is the largest integer such that every pair mapping on `n` points has an independent
set of size at least `g n`. Equivalently, it is the minimum of `independenceNumber` over all
pair mappings. If no pair mapping exists (only possible for `n = 2`), this is `0`.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {m | ∃ f : Fin n → Fin n → Fin n, IsPairMapping f ∧ independenceNumber f = m}

/--
Let $f$ be a function from all pairs of elements in $\{1,\ldots,n\}$ to $\{1,\ldots,n\}$
such that $f(x,y)\neq x$ and $\neq y$ for all $x,y$.
We call $X\subseteq \{1,\ldots,n\}$ independent if whenever $x,y\in X$ we have
$f(x,y)\not\in X$.

Let $g(n)$ be such that, in every function $f$, there is an independent set of size at
least $g(n)$. Estimate $g(n)$.

A question of Erdős and Hajnal [ErHa58], who could prove
$$n^{1/3} \ll g(n) \ll (n\log n)^{1/2}.$$
Spencer [Sp72] proved $g(n)\gg n^{1/2}$.
Conlon, Fox, and Sudakov [CFS16] proved $g(n)\ll n^{1/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1025 :
    (fun n => (g n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/--
Erdős and Hajnal [ErHa58] proved $n^{1/3} \ll g(n)$.
-/
@[category research solved, AMS 5]
theorem erdos_1025.variants.erdos_hajnal_lower :
    (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) ≪ (fun n => (g n : ℝ)) := by
  sorry

/--
Erdős and Hajnal [ErHa58] proved $g(n) \ll (n\log n)^{1/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1025.variants.erdos_hajnal_upper :
    (fun n => (g n : ℝ)) ≪
      (fun n : ℕ => ((n : ℝ) * Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

/-- Spencer [Sp72] proved $g(n)\gg n^{1/2}$. -/
@[category research solved, AMS 5]
theorem erdos_1025.variants.spencer :
    (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) ≪ (fun n => (g n : ℝ)) := by
  sorry

/-- Conlon, Fox, and Sudakov [CFS16] proved $g(n)\ll n^{1/2}$. -/
@[category research solved, AMS 5]
theorem erdos_1025.variants.conlon_fox_sudakov :
    (fun n => (g n : ℝ)) ≪ (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) := by
  sorry

/-- The empty set is independent for every function on pairs. -/
@[category test, AMS 5]
theorem isIndependent_empty {n : ℕ} (f : Fin n → Fin n → Fin n) :
    IsIndependent f ∅ := by
  simp [IsIndependent]

end Erdos1025

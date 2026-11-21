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
# Erdős Problem 186

*References:*
- [erdosproblems.com/186](https://www.erdosproblems.com/186)
- [Bo89] Bosznay, Á. P., *On the lower estimation of nonaveraging sets*. Acta Math. Hungar.
  (1989), 155-157.
- [ErSa90] Erdős, P. and Sárközy, A., *On a problem of Straus*. Disorder in physical systems
  (1990), 55-66.
- [PhZa24] Pham, H. T. and Zakharov, D., *Sharp bound for the Erdős–Straus non-averaging set
  problem*. [arXiv:2410.14624](https://arxiv.org/abs/2410.14624) (2024).
-/

@[expose] public section

open Filter Topology

namespace Erdos186

/-- A finite set $A$ of natural numbers is *non-averaging* if no $a \in A$ is the arithmetic mean
of at least two other elements of $A$: there is no $S \subseteq A \setminus \{a\}$ with
$|S| \geq 2$ and $\sum_{x \in S} x = |S| \cdot a$. This agrees with [PhZa24] ("a nonempty subset of
$A$ not containing $a$"), since a single element other than $a$ never has mean $a$. -/
def NonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, 2 ≤ S.card → (∑ x ∈ S, x) ≠ S.card * a

instance (A : Finset ℕ) : Decidable (NonAveraging A) := by
  unfold NonAveraging; infer_instance

/-- $F(N)$ is the maximal size of a non-averaging subset of $\{1, \dots, N\}$. -/
def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonAveraging).sup Finset.card

/-- Every non-averaging $A \subseteq \{1, \dots, N\}$ has at most $F(N)$ elements. -/
@[category API, AMS 11]
theorem card_le_F {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    A.card ≤ F N :=
  Finset.le_sup (f := Finset.card) (by simp [hA, hna])

/-- $\{1, 2, 3\}$ is not non-averaging, since $2$ is the mean of $1$ and $3$. -/
@[category test, AMS 11]
theorem not_nonAveraging_one_two_three : ¬ NonAveraging {1, 2, 3} := by
  decide

/-- $\{1, 2, 4\}$ is non-averaging. -/
@[category test, AMS 11]
theorem nonAveraging_one_two_four : NonAveraging {1, 2, 4} := by
  decide

/--
Let $F(N)$ be the maximal size of $A\subseteq \{1,\ldots,N\}$ which is 'non-averaging', so that
no $n\in A$ is the arithmetic mean of at least two elements in $A$. What is the order of growth
of $F(N)$?

It is known that $N^{1/4}\ll F(N) \ll N^{1/4+o(1)}$: the lower bound is due to Bosznay [Bo89] and
the upper bound to Pham and Zakharov [PhZa24, Theorem 1]. So $\log F(N)/\log N\to 1/4$.
-/
@[category research solved, AMS 11]
theorem erdos_186 :
    Tendsto (fun N : ℕ ↦ Real.log (F N) / Real.log N) atTop (𝓝 (1 / 4)) := by
  sorry

/--
Pham and Zakharov [PhZa24, Theorem 1] proved that every non-averaging subset of
$\{1,\ldots,N\}$ has size at most $N^{1/4+o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_186.variants.pham_zakharov :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

/-- The lower bound $N^{1/4}\ll F(N)$ is due to Bosznay [Bo89]. -/
@[category research solved, AMS 11]
theorem erdos_186.variants.bosznay :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 4) ≤ F N := by
  sorry

/-- The original upper bound of Erdős and Sárközy [ErSa90] was $F(N)\ll (N\log N)^{1/2}$. -/
@[category research solved, AMS 11]
theorem erdos_186.variants.erdos_sarkozy :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (F N : ℝ) ≤ C * Real.sqrt ((N : ℝ) * Real.log N) := by
  sorry

end Erdos186

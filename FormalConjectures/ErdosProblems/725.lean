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
# Erdős Problem 725

*References:*
- [erdosproblems.com/725](https://www.erdosproblems.com/725)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica 1 (1981), 25-42. [PDF](https://www.renyi.hu/~p_erdos/1981-16.pdf)
- [ErKa46] Erdős, P. and Kaplansky, I., *The asymptotic number of Latin rectangles*.
  Amer. J. Math. 68 (1946), 230-236. [PDF](https://www.renyi.hu/~p_erdos/1946-12.pdf)
- [Ya51] Yamamoto, K., *On the asymptotic number of Latin rectangles*.
  Jpn. J. Math. 21 (1951), 113-119.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos725

/-- `M` is a $k\times n$ Latin rectangle: `M i j` is the entry in row `i` and column `j`, the
entries are in `Fin n` (standing for $\{1,\dots,n\}$), every row is a permutation of the
entries, and no entry is repeated in a column. -/
abbrev IsLatinRectangle {k n : ℕ} (M : Fin k → Fin n → Fin n) : Prop :=
  (∀ i, Function.Injective (M i)) ∧ ∀ j, Function.Injective fun i ↦ M i j

/-- $L(k,n)$ is the number of $k\times n$ Latin rectangles. Rows, columns and entries are
labelled and the rows are ordered. It is $0$ for $k>n\geq 1$ and $1$ for $k=0$. -/
noncomputable def L (k n : ℕ) : ℕ :=
  Nat.card {M : Fin k → Fin n → Fin n // IsLatinRectangle M}

/-- There are $n!$ Latin rectangles with one row. -/
@[category test, AMS 5]
theorem L_one (n : ℕ) : L 1 n = n.factorial := by
  have e : {M : Fin 1 → Fin n → Fin n // IsLatinRectangle M} ≃ Equiv.Perm (Fin n) :=
    { toFun := fun M ↦ Equiv.ofBijective (M.1 0) (Finite.injective_iff_bijective.1 (M.2.1 0))
      invFun := fun σ ↦ ⟨fun _ ↦ σ, fun _ ↦ σ.injective, fun _ a b _ ↦ Subsingleton.elim a b⟩
      left_inv := fun M ↦ by
        refine Subtype.ext (funext fun i ↦ ?_)
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        rfl
      right_inv := fun σ ↦ Equiv.ext fun _ ↦ rfl }
  unfold L
  rw [Nat.card_congr e, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

def erdos_725.answer : ℕ → ℕ → ℝ := sorry

/--
Give an asymptotic formula for the number of $k\times n$ Latin rectangles.

The formula $F(k,n)$ must satisfy $L(k,n)\sim F(k,n)$ as $n\to\infty$ for every choice of
$k=k(n)\leq n$, so it also covers Latin squares ($k=n$).
-/
@[category research open, question value, AMS 5]
theorem erdos_725 (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n) :
    (fun n ↦ (L (k n) n : ℝ)) ~[atTop] fun n ↦ erdos_725.answer (k n) n := by
  sorry

/--
Erdős and Kaplansky [ErKa46] proved the count is
$$\sim e^{-\binom{k}{2}}(n!)^k$$
when $k=o((\log n)^{3/2-\epsilon})$.

Here $\epsilon>0$ is fixed.
-/
@[category research solved, AMS 5]
theorem erdos_725.variants.erdos_kaplansky (ε : ℝ) (hε : 0 < ε) (k : ℕ → ℕ)
    (hk : (fun n ↦ (k n : ℝ)) =o[atTop] fun n ↦ Real.log n ^ (3 / 2 - ε)) :
    (fun n ↦ (L (k n) n : ℝ)) ~[atTop]
      fun n ↦ Real.exp (-((k n).choose 2 : ℝ)) * (n.factorial : ℝ) ^ k n := by
  sorry

/--
Yamamoto [Ya51] extended this to $k\leq n^{1/3-o(1)}$.

As in [Ya51, p. 113], we assume $k<n^{1/3-\delta}$ with $n^{-\delta}\to 0$, where $\delta$
may be a positive constant or a function of $n$.
-/
@[category research solved, AMS 5]
theorem erdos_725.variants.yamamoto (δ : ℕ → ℝ)
    (hδ : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-δ n)) atTop (nhds 0)) (k : ℕ → ℕ)
    (hk : ∀ᶠ n in atTop, (k n : ℝ) < (n : ℝ) ^ (1 / 3 - δ n)) :
    (fun n ↦ (L (k n) n : ℝ)) ~[atTop]
      fun n ↦ Real.exp (-((k n).choose 2 : ℝ)) * (n.factorial : ℝ) ^ k n := by
  sorry

end Erdos725

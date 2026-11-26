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
# Erdős Problem 724

*References:*
- [erdosproblems.com/724](https://www.erdosproblems.com/724)
- [OEIS A001438](https://oeis.org/A001438)
- [Be83c] Beth, Thomas, *Eine Bemerkung zur Abschätzung der Anzahl orthogonaler lateinischer
  Quadrate mittels Siebverfahren*. Abh. Math. Sem. Univ. Hamburg (1983), 284-288.
- [BPS60] Bose, R. C. and Shrikhande, S. S. and Parker, E. T., *Further results on the
  construction of mutually orthogonal Latin squares and the falsity of Euler's conjecture*.
  Canadian J. Math. (1960), 189-203.
- [CES60] Chowla, S. and Erdős, P. and Straus, E. G., *On the maximal number of pairwise
  orthogonal Latin squares of a given order*. Canadian J. Math. (1960), 204-208.
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Wi74] Wilson, Richard M., *Concerning the number of mutually orthogonal Latin squares*.
  Discrete Math. (1974), 181-198.
-/

@[expose] public section

open Filter Finset

namespace Erdos724

/--
Two Latin squares $L, M$ of order $n$ are orthogonal if superimposing them gives each ordered
pair of symbols at most once, i.e. the map $(i, j) \mapsto (L_{ij}, M_{ij})$ is injective
(hence bijective).
-/
def IsOrthogonal {n : ℕ} (L M : LatinSquare n) : Prop :=
  Function.Injective fun p : Fin n × Fin n => (L.mat p.1 p.2, M.mat p.1 p.2)

/--
`maxMOLS n` is $f(n)$, the maximum number of mutually orthogonal Latin squares of order $n$:
the largest size of a set of Latin squares of order $n$ that are pairwise orthogonal. For
$n \leq 1$ this gives $f(n) = 1$, while OEIS A001438 uses $\infty$.
-/
noncomputable def maxMOLS (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}

/--
Let $f(n)$ be the maximum number of mutually orthogonal Latin squares of order $n$. Is it true
that
$$f(n) \gg n^{1/2}?$$
This question is from [Er81].
-/
@[category research open, question, AMS 5]
theorem erdos_724 :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.sqrt (n : ℝ) ≤ (maxMOLS n : ℝ) := by
  sorry

/-- The entries of `latinSquare10` (found by a computer search for an orthogonal pair). -/
def latinSquare10Mat : Matrix (Fin 10) (Fin 10) (Fin 10) :=
  !![0, 1, 2, 3, 4, 5, 6, 7, 8, 9;
    1, 0, 5, 2, 7, 9, 8, 3, 6, 4;
    8, 6, 0, 9, 1, 3, 7, 2, 4, 5;
    5, 8, 1, 6, 3, 0, 9, 4, 7, 2;
    4, 5, 6, 0, 2, 7, 3, 9, 1, 8;
    7, 2, 9, 5, 8, 1, 4, 6, 0, 3;
    2, 4, 3, 7, 5, 6, 1, 8, 9, 0;
    9, 7, 8, 1, 0, 4, 2, 5, 3, 6;
    6, 3, 4, 8, 9, 2, 0, 1, 5, 7;
    3, 9, 7, 4, 6, 8, 5, 0, 2, 1]

/-- The entries of `orthogonalMate10`. -/
def orthogonalMate10Mat : Matrix (Fin 10) (Fin 10) (Fin 10) :=
  !![0, 1, 2, 3, 4, 5, 6, 7, 8, 9;
    9, 7, 1, 5, 6, 8, 3, 2, 4, 0;
    7, 0, 3, 6, 5, 4, 8, 9, 1, 2;
    6, 5, 4, 9, 0, 1, 7, 8, 2, 3;
    2, 3, 8, 4, 7, 0, 9, 5, 6, 1;
    3, 4, 0, 8, 2, 7, 5, 1, 9, 6;
    8, 6, 7, 1, 9, 2, 0, 4, 3, 5;
    4, 9, 6, 2, 8, 3, 1, 0, 5, 7;
    5, 8, 9, 0, 1, 6, 2, 3, 7, 4;
    1, 2, 5, 7, 3, 9, 4, 6, 0, 8]

/-- A Latin square of order $10$ that is orthogonal to `orthogonalMate10`. -/
def latinSquare10 : LatinSquare 10 where
  mat := latinSquare10Mat
  row_injective := by
    show ∀ i, Function.Injective fun j ↦ latinSquare10Mat i j
    decide +kernel
  col_injective := by
    show ∀ j, Function.Injective fun i ↦ latinSquare10Mat i j
    decide +kernel

/-- A Latin square of order $10$ that is orthogonal to `latinSquare10`. -/
def orthogonalMate10 : LatinSquare 10 where
  mat := orthogonalMate10Mat
  row_injective := by
    show ∀ i, Function.Injective fun j ↦ orthogonalMate10Mat i j
    decide +kernel
  col_injective := by
    show ∀ j, Function.Injective fun i ↦ orthogonalMate10Mat i j
    decide +kernel

/--
Euler conjectured that $f(n) = 1$ when $n \equiv 2 \pmod{4}$. This is false: Bose, Parker, and
Shrikhande [BPS60] proved $f(n) \geq 2$ for $n \geq 7$, so for example $f(10) \geq 2$.

The proof below checks the explicit orthogonal pair `latinSquare10`, `orthogonalMate10`.
-/
@[category research solved, question, AMS 5]
theorem erdos_724.variants.euler_conjecture :
    ¬ ∀ n : ℕ, n ≡ 2 [MOD 4] → maxMOLS n = 1 := by
  intro h
  have hLM : IsOrthogonal latinSquare10 orthogonalMate10 := by
    unfold IsOrthogonal
    decide +kernel
  have hne : latinSquare10 ≠ orthogonalMate10 := fun h' ↦
    absurd (congrArg (fun L : LatinSquare 10 ↦ L.mat 1 0) h') (by decide +kernel)
  have h2 : 2 ≤ maxMOLS 10 := by
    classical
    refine le_csSup ⟨Fintype.card (LatinSquare 10), ?_⟩
      ⟨{latinSquare10, orthogonalMate10}, card_pair hne, ?_⟩
    · rintro k ⟨S, rfl, -⟩
      exact card_le_univ S
    · rw [coe_pair, Set.pairwise_pair]
      exact fun _ ↦ ⟨hLM, fun p q hpq ↦ hLM (congrArg Prod.swap hpq)⟩
  have := h 10 rfl
  omega

/--
Bose, Parker, and Shrikhande [BPS60] proved that $f(n) \geq 2$ for all $n \geq 7$.
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.bose_parker_shrikhande :
    ∀ n : ℕ, 7 ≤ n → 2 ≤ maxMOLS n := by
  sorry

/--
Chowla, Erdős, and Straus [CES60] proved that
$$f(n) \gg n^{1/91}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.chowla_erdos_straus :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 91) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
Wilson [Wi74] proved that
$$f(n) \gg n^{1/17}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.wilson :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 17) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
Beth [Be83c] proved that
$$f(n) \gg n^{1/14.8}.$$
-/
@[category research solved, AMS 5]
theorem erdos_724.variants.beth :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((1 : ℝ) / 14.8) ≤ (maxMOLS n : ℝ) := by
  sorry

/--
For $n \geq 2$ there are at most $n - 1$ mutually orthogonal Latin squares of order $n$:
$$f(n) \leq n - 1.$$
This is classical; see OEIS A001438.
-/
@[category textbook, AMS 5]
theorem erdos_724.variants.le_sub_one :
    ∀ n : ℕ, 2 ≤ n → maxMOLS n ≤ n - 1 := by
  intro n hn
  apply csSup_le'
  rintro k ⟨S, rfl, hS⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  -- `c L` is the column of row `i0` that holds the symbol of cell `(i1, i0)`.
  let c : LatinSquare n → Fin n := fun L ↦
    (Equiv.ofBijective (L.mat i0) (Finite.injective_iff_bijective.1 (L.row_injective i0))).symm
      (L.mat i1 i0)
  have hc : ∀ L : LatinSquare n, L.mat i0 (c L) = L.mat i1 i0 := fun L ↦
    Equiv.ofBijective_apply_symm_apply _ _ _
  -- `c L ≠ i0`, since column `i0` has no repeated symbol.
  have hc0 : ∀ L : LatinSquare n, c L ≠ i0 := by
    intro L h
    have h' := hc L
    rw [h] at h'
    exact h01 (L.col_injective i0 h')
  -- Orthogonal squares have different `c`: otherwise their pairs agree at `(i0, c)` and `(i1, i0)`.
  have hinj : Set.InjOn c S := by
    intro L hL M hM hLM
    by_contra hne
    have horth : IsOrthogonal L M := hS hL hM hne
    have := @horth (i0, c L) (i1, i0)
      (show (L.mat i0 (c L), M.mat i0 (c L)) = (L.mat i1 i0, M.mat i1 i0) by
        rw [hc L, hLM, hc M])
    exact h01 (congrArg Prod.fst this)
  calc #S = #(S.image c) := (Finset.card_image_of_injOn hinj).symm
    _ ≤ #((Finset.univ : Finset (Fin n)).erase i0) := Finset.card_le_card fun x hx ↦ by
        obtain ⟨L, -, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_erase.2 ⟨hc0 L, Finset.mem_univ _⟩
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

end Erdos724

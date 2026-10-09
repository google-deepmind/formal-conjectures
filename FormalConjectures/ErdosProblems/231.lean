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
# Erdős Problem 231

*References:*
- [erdosproblems.com/231](https://www.erdosproblems.com/231)
- [Er57] Erdős, Paul, *Some unsolved problems*. Michigan Math. J. (1957), 291-300.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Ke92] Keränen, Veikko, *Abelian squares are avoidable on $4$ letters*. Automata, languages and
  programming (Vienna, 1992) (1992), 41-52.
- [FiPu23] Fici, Gabriele and Puzynina, Svetlana, *Abelian combinatorics on words: a survey*.
  Comput. Sci. Rev. (2023), Paper No. 100532, 21.
-/

@[expose] public section

namespace Erdos231

/-- A string `S` contains an abelian square if it has two consecutive nonempty blocks `x` and `y`
such that `y` is a permutation of `x`. -/
def ContainsAbelianSquare {α : Type*} (S : List α) : Prop :=
  ∃ x y : List α, x ≠ [] ∧ x.Perm y ∧ x ++ y <:+: S

/-- `S` contains an abelian square iff two consecutive blocks of some positive length `L` of `S`
are permutations of each other. -/
@[category API, AMS 5]
theorem containsAbelianSquare_iff {α : Type*} (S : List α) :
    ContainsAbelianSquare S ↔ ∃ i < S.length, ∃ L < S.length, 0 < L ∧ i + 2 * L ≤ S.length ∧
      ((S.drop i).take L).Perm ((S.drop (i + L)).take L) := by
  constructor
  · rintro ⟨x, y, hx, hxy, s, t, hS⟩
    have hlen : x.length = y.length := hxy.length_eq
    have hxpos : 0 < x.length := List.length_pos_of_ne_nil hx
    refine ⟨s.length, ?_, x.length, ?_, hxpos, ?_, ?_⟩
    · rw [← hS]; simp; omega
    · rw [← hS]; simp; omega
    · rw [← hS]; simp; omega
    · have h1 : (S.drop s.length).take x.length = x := by
        rw [← hS, List.append_assoc, List.drop_left, List.append_assoc, List.take_left]
      have h2 : (S.drop (s.length + x.length)).take x.length = y := by
        rw [← hS, ← List.length_append, show s ++ (x ++ y) ++ t = (s ++ x) ++ (y ++ t) by
          simp only [List.append_assoc], List.drop_left, List.take_left' hlen.symm]
      rw [h1, h2]
      exact hxy
  · rintro ⟨i, -, L, -, hL, hle, hperm⟩
    refine ⟨(S.drop i).take L, (S.drop (i + L)).take L, ?_, hperm, ?_⟩
    · intro h
      have := congrArg List.length h
      simp only [List.length_take, List.length_drop, List.length_nil] at this
      omega
    · have : (S.drop i).take L ++ (S.drop (i + L)).take L = (S.drop i).take (L + L) := by
        rw [List.take_add, List.drop_drop]
      rw [this]
      exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

instance {α : Type*} [DecidableEq α] (S : List α) : Decidable (ContainsAbelianSquare S) :=
  decidable_of_iff _ (containsAbelianSquare_iff S).symm

/-- The string $1213121412132124$ of length $2^4$ over four characters contains no abelian
square. -/
@[category API, AMS 5]
theorem not_containsAbelianSquare_example :
    ¬ ContainsAbelianSquare ([0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1, 3] : List (Fin 4)) := by
  decide +kernel

/-- Every string of length $4$ over two characters contains an abelian square. -/
@[category API, AMS 5]
theorem containsAbelianSquare_of_length_four (f : Fin 4 → Fin 2) :
    ContainsAbelianSquare (List.ofFn f) := by
  revert f
  decide +kernel

set_option maxRecDepth 200000 in
/-- Every string of length $8$ over three characters contains an abelian square. -/
@[category API, AMS 5]
theorem containsAbelianSquare_of_length_eight (f : Fin 8 → Fin 3) :
    ContainsAbelianSquare (List.ofFn f) := by
  revert f
  decide +kernel

/--
Let $S$ be a string of length $2^k-1$ formed from an alphabet of $k$ characters. Must $S$ contain
an abelian square: two consecutive blocks $x$ and $y$ such that $y$ is a permutation of $x$?

Erdős initially conjectured that the answer is yes for all $k\geq 2$, but for $k=4$ this was
disproved by de Bruijn and Erdős. Erdős then asked if there is in fact an infinite string formed
from $\{1,2,3,4\}$ which contains no abelian squares? This is equivalent to
[192](https://www.erdosproblems.com/192), and such a string was constructed by Keränen [Ke92]. The
existence of this infinite string gives a negative answer to the problem for all $k\geq 4$.

Containing no abelian squares is a stronger property than being squarefree (the existence of
infinitely long squarefree strings over alphabets with $k\geq 3$ characters was established by
Thue). We refer to a recent survey by Fici and Puzynina [FiPu23] for more background and related
results.

As stated, the answer is negative for every $k \geq 2$: the strings $121$ and $1213121$ of
length $2^k - 1$ for $k = 2, 3$ contain no abelian square. See `erdos_231.variants.two_pow` for
strings of length $2^k$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos231.lean#L38"]
theorem erdos_231 : answer(False) ↔
    ∀ k : ℕ, 2 ≤ k → ∀ S : List (Fin k), S.length = 2 ^ k - 1 → ContainsAbelianSquare S := by
  sorry

/--
Perhaps Erdős meant $2^k$, where indeed there is an example for $k=4$:
$$1213121412132124.$$
Every string of length $2^k$ over $k$ characters contains an abelian square for $k = 2, 3$, but
not for $k \geq 4$.
-/
@[category research solved, AMS 5]
theorem erdos_231.variants.two_pow : answer(False) ↔
    ∀ k : ℕ, 2 ≤ k → ∀ S : List (Fin k), S.length = 2 ^ k → ContainsAbelianSquare S := by
  show False ↔ _
  simp only [false_iff]
  intro h
  exact not_containsAbelianSquare_example (h 4 (by norm_num) _ rfl)

/-- Every string of length $2^k$ over $k$ characters contains an abelian square for $k = 2, 3$. -/
@[category research solved, AMS 5]
theorem erdos_231.variants.two_pow_small (k : ℕ) (hk : k = 2 ∨ k = 3) (S : List (Fin k))
    (hS : S.length = 2 ^ k) : ContainsAbelianSquare S := by
  have key : ∀ {α : Type} (S : List α) {n : ℕ}, S.length = n → ∃ f : Fin n → α, S = List.ofFn f :=
    fun S n h => by subst h; exact ⟨S.get, (List.ofFn_get S).symm⟩
  rcases hk with rfl | rfl
  · obtain ⟨f, rfl⟩ := key S hS
    exact containsAbelianSquare_of_length_four f
  · obtain ⟨f, rfl⟩ := key S hS
    exact containsAbelianSquare_of_length_eight f

end Erdos231

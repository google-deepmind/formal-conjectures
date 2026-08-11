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
# Ben Green's Open Problem 21

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.21)
- [Ra33] Rado, Richard, *Studien zur Kombinatorik*. Math. Zeit. 36 (1933), 242-280.
- [FoKl06] Fox, Jacob and Kleitman, Daniel, *On Rado's boundedness conjecture*. J. Combin. Theory
  Ser. A 113 (2006), no. 1, 84-100.
- [ElJo23] Ellis, David and Johnson, Robert (editors), *A collection of open problems in
  celebration of Imre Leader's 60th birthday*. arXiv preprint arXiv:2310.18163 (2023).
-/

open Finset

namespace Green21

/--
The coefficients $a_1, \dots, a_k$ satisfy **Rado's condition** if $\sum_{i \in I} a_i = 0$ for
some non-empty $I \subseteq [k]$.

For a single homogeneous equation this is exactly the criterion of Rado's theorem [Ra33]:
$a_1x_1 + \cdots + a_kx_k = 0$ is partition regular if and only if the coefficients satisfy it.
-/
def RadoCondition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ I : Finset (Fin k), I.Nonempty ∧ ∑ i ∈ I, a i = 0

/--
$c(a_1, \dots, a_k)$, the least number of colours required in order to colour $\mathbb{N}$ so
that there is no monochromatic solution to $a_1x_1 + \cdots + a_kx_k = 0$.

The solutions $x_i$ are required to be *positive*, as in [FoKl06]: were $0$ admitted then
$x_1 = \cdots = x_k = 0$ would be a monochromatic solution for every colouring, and no number of
colours would ever suffice. The $x_i$ are not required to be distinct.

When the coefficients do not satisfy `RadoCondition`, Rado's theorem [Ra33] guarantees that some
finite colouring has no monochromatic solution, so the set below is non-empty and this `sInf` is
a genuine minimum.
-/
noncomputable def minColours {k : ℕ} (a : Fin k → ℤ) : ℕ :=
  sInf {r | ∃ col : ℕ → Fin r, ∀ x : Fin k → ℕ, (∀ i, 0 < x i) →
    (∀ i j, col (x i) = col (x j)) → ∑ i, a i * x i ≠ 0}

/--
Suppose that $a_1, \dots, a_k$ are integers which do not satisfy Rado's condition: thus if
$\sum_{i \in I} a_i = 0$ then $I = \emptyset$. It then follows from Rado's theorem that the
equation $a_1x_1 + \cdots + a_kx_k = 0$ is not partition regular. Write $c(a_1, \dots, a_k)$ for
the least number of colours required in order to colour $\mathbb{N}$ so that there is no
monochromatic solution to $a_1x_1 + \cdots + a_kx_k = 0$. Is $c(a_1, \dots, a_k)$ bounded in
terms of $k$ only?

This problem, which is known as Rado's boundedness conjecture, dates back to 1933 [Ra33]. It is
open for all $k \geq 4$.
-/
@[category research open, AMS 5 11]
theorem green_21 : answer(sorry) ↔ ∃ B : ℕ → ℕ, ∀ (k : ℕ) (a : Fin k → ℤ),
    ¬ RadoCondition a → minColours a ≤ B k := by
  sorry

/--
The answer was shown to be affirmative for $k = 3$ by Fox and Kleitman [FoKl06], who showed that
$c(a_1, a_2, a_3) \leq 24$.
-/
@[category research solved, AMS 5 11]
theorem green_21.variants.fox_kleitman (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    minColours a ≤ 24 := by
  sorry

/--
Green [Gr24] is not sure that the constant $24$ of [FoKl06] is sharp, and remarks that it might
be interesting to determine the sharp constant.

The largest value of $c(a_1, a_2, a_3)$ is attained, since by `green_21.variants.fox_kleitman`
the values form a non-empty set of naturals bounded above by $24$.
-/
@[category research open, AMS 5 11]
theorem green_21.variants.fox_kleitman_sharp :
    IsGreatest {c | ∃ a : Fin 3 → ℤ, ¬ RadoCondition a ∧ minColours a = c} answer(sorry) := by
  sorry

/--
A question [FoKl06, Conjecture 5] of Fox and Kleitman, which they call a 'modular analogue' of
Rado's Boundedness Conjecture. Let $p$ be a prime, and suppose that $a_1, \dots, a_k$ are
integers with $\sum_{i \in I} a_i \equiv 0 \pmod p$ only when $I = \emptyset$. Does there exist
an $f(k)$-colouring of $(\mathbb{Z}/p\mathbb{Z})^*$ with no monochromatic solution to
$a_1x_1 + \cdots + a_kx_k = 0$? This seems to be open even when $k = 3$; Green [Gr24] suspects
the answer may be negative.

The point of the question is that the number of colours $f(k)$ must not depend on $p$.
-/
@[category research open, AMS 5 11]
theorem green_21.variants.fox_kleitman_modular : answer(sorry) ↔ ∃ f : ℕ → ℕ,
    ∀ (k p : ℕ), p.Prime → ∀ a : Fin k → ℤ,
      (∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) →
      ∃ col : (ZMod p)ˣ → Fin (f k), ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  sorry

/--
The largest $d \leq r$ such that $\sum_{i \in I} a_i \equiv 0 \pmod{2^d}$ for some non-empty
subset $I \subseteq [k]$, where $a_1, \dots, a_k \in \mathbb{Z}/2^r\mathbb{Z}$.

Congruence mod $2^d$ of an element of $\mathbb{Z}/2^r\mathbb{Z}$ is expressed through its
canonical representative `ZMod.val`; this is unambiguous because $d$ is capped at $r$.
-/
noncomputable def maxDepth {k r : ℕ} (a : Fin k → ZMod (2 ^ r)) : ℕ :=
  sSup {d | d ≤ r ∧ ∃ I : Finset (Fin k), I.Nonempty ∧ 2 ^ d ∣ (∑ i ∈ I, a i).val}

/--
Milićević [ElJo23, Conjecture 11.1] conjectures the following 2-adic variant. For any
$k \in \mathbb{N}$, there exists $K = K(k)$ such that the following is true. Let $r$ be a
positive integer, and let $a_1, \dots, a_k \in \mathbb{Z}/2^r\mathbb{Z}$. Let $d$ be the largest
integer such that $\sum_{i \in I} a_i \equiv 0 \pmod{2^d}$ for some non-empty subset
$I \subset [k]$. Then there is a $K$-colouring of $\mathbb{Z}/2^r\mathbb{Z}$ such that all
monochromatic solutions $x = (x_1, \dots, x_k)$ to the equation
$a_1x_1 + \cdots + a_kx_k = 0$ satisfy $x_i \equiv 0 \pmod{2^{r-d}}$ for all $i = 1, \dots, k$.

Milićević remarks that, if true, this would imply the Rado boundedness conjecture by a
compactness argument.
-/
@[category research open, AMS 5 11]
theorem green_21.variants.milicevic : ∀ k : ℕ, ∃ K : ℕ, ∀ r : ℕ, 0 < r →
    ∀ a : Fin k → ZMod (2 ^ r), ∃ col : ZMod (2 ^ r) → Fin K,
      ∀ x : Fin k → ZMod (2 ^ r), (∀ i j, col (x i) = col (x j)) →
        ∑ i, a i * x i = 0 → ∀ i, 2 ^ (r - maxDepth a) ∣ (x i).val := by
  sorry

/--
Not satisfying `RadoCondition` is Green's phrasing "if $\sum_{i \in I} a_i = 0$ then
$I = \emptyset$".
-/
@[category test, AMS 5 11]
theorem not_radoCondition_iff {k : ℕ} (a : Fin k → ℤ) :
    ¬ RadoCondition a ↔ ∀ I : Finset (Fin k), ∑ i ∈ I, a i = 0 → I = ∅ := by
  simp only [RadoCondition, not_exists, not_and, Finset.nonempty_iff_ne_empty]
  exact ⟨fun h I hI => by_contra fun hne => h I hne hI, fun h I hne hI => hne (h I hI)⟩

/--
A tuple failing `RadoCondition` has no zero coefficient, since a singleton is a non-empty subset.
-/
@[category test, AMS 5 11]
theorem ne_zero_of_not_radoCondition {k : ℕ} {a : Fin k → ℤ} (ha : ¬ RadoCondition a) (i : Fin k) :
    a i ≠ 0 := fun h => ha ⟨{i}, Finset.singleton_nonempty i, by simpa using h⟩

/--
In the degenerate case $k = 0$ the equation reads $0 = 0$, so the empty tuple is a monochromatic
solution for every colouring and `minColours` takes its junk value `0`. The bound asserted by
`green_21` is therefore vacuously satisfied at $k = 0$, and the content of the problem is
unaffected.
-/
@[category test, AMS 5 11]
theorem minColours_eq_zero (a : Fin 0 → ℤ) : minColours a = 0 := by
  have : {r | ∃ col : ℕ → Fin r, ∀ x : Fin 0 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, a i * x i ≠ 0} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    exact fun col h => h (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (by simp)
  rw [minColours, this, Nat.sInf_empty]

/--
A case where the infimum defining `minColours` is a genuine minimum rather than the junk value of
`sInf ∅`. The coefficients $(1, 1, 1)$ fail `RadoCondition`, and since the $x_i$ are positive the
equation $x_1 + x_2 + x_3 = 0$ has no solutions at all, so a single colour suffices; no colouring
of $\mathbb{N}$ into `Fin 0` exists, so $0$ is not attainable.
-/
@[category test, AMS 5 11]
theorem minColours_ones : minColours ![(1 : ℤ), 1, 1] = 1 := by
  have h1 : 1 ∈ {r | ∃ col : ℕ → Fin r, ∀ x : Fin 3 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, (![(1 : ℤ), 1, 1]) i * x i ≠ 0} := by
    refine ⟨fun _ => 0, fun x hx _ => ?_⟩
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, one_mul]
    omega
  have h0 : 0 ∉ {r | ∃ col : ℕ → Fin r, ∀ x : Fin 3 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, (![(1 : ℤ), 1, 1]) i * x i ≠ 0} := by
    rintro ⟨col, -⟩
    exact (col 0).elim0
  rw [minColours]
  exact le_antisymm (Nat.sInf_le h1) (Nat.one_le_iff_ne_zero.2 fun h =>
    h0 ((Nat.sInf_eq_zero.mp h).resolve_right (Set.nonempty_iff_ne_empty.mp ⟨1, h1⟩)))

end Green21

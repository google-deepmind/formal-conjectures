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
# Erdős Problem 709

*References:*
- [erdosproblems.com/709](https://www.erdosproblems.com/709)
- [ErSu59] P. Erdős and J. Surányi, Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs, Mat. Lapok 10 (1959), 39–48.
- [Er92c] P. Erdős, Some of my forgotten problems in number theory, Hardy–Ramanujan J. 15
  (1992), 34–50.
- [vD26] W. van Doorn, On the length of an interval that contains distinct multiples of the
  first $n$ positive integers, Integers (2026), #A7.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos709

/-- The block of `length` consecutive positive integers immediately after `start`. -/
def window (start length : ℕ) : Finset ℕ := Finset.Icc (start + 1) (start + length)

/-- A block contains distinct multiples of all elements of `A`. -/
def HasDistinctMultiples (A : Finset ℕ) (start length : ℕ) : Prop :=
  ∃ choice : ℕ → ℕ,
    Set.InjOn choice (A : Set ℕ) ∧
    ∀ a ∈ A, choice a ∈ window start length ∧ a ∣ choice a

/-- The multiplier `k` works for all `n`-element inputs and all starting points.
`M` is required to be the largest element of `A`. -/
def Works (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ),
    A.card = n → M ∈ A → (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) →
    ∀ start : ℕ, HasDistinctMultiples A start (k * M)

/-- `k` is the least multiplier that works for inputs of size `n`. -/
def IsOptimal (n k : ℕ) : Prop := Works n k ∧ ∀ j < k, ¬ Works n j

/-- A matching in a shorter block remains a matching in any longer block. -/
@[category API, AMS 5 11]
theorem matching_mono_length
    (A : Finset ℕ) (start small large : ℕ) (hsmall : small ≤ large)
    (h : HasDistinctMultiples A start small) : HasDistinctMultiples A start large := by
  obtain ⟨choice, hinj, hchoice⟩ := h
  refine ⟨choice, hinj, ?_⟩
  intro a ha
  obtain ⟨hmem, hdvd⟩ := hchoice a ha
  refine ⟨?_, hdvd⟩
  simp only [window, Finset.mem_Icc] at hmem ⊢
  constructor
  · exact hmem.1
  · omega

/-- If multiplier `k` works, every larger multiplier also works. -/
@[category API, AMS 5 11]
theorem works_mono (n k l : ℕ) (hkl : k ≤ l) (h : Works n k) : Works n l := by
  intro A M hcard hmax hbound htwo start
  exact matching_mono_length A start (k * M) (l * M) (Nat.mul_le_mul_right M hkl)
    (h A M hcard hmax hbound htwo start)

/-- Every interval of `M` consecutive positive integers contains a multiple of `a` when
`0 < a ≤ M`. -/
@[category API, AMS 5 11]
theorem exists_multiple_in_window
    (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    ∃ b ∈ window start M, a ∣ b := by
  let r := start % a
  let b := start + (a - r)
  have hr : r < a := Nat.mod_lt start ha
  have heq : start % a + a * (start / a) = start := by
    simpa [Nat.mul_comm] using Nat.mod_add_div start a
  have hbdiv : b = a * (start / a + 1) := by
    have haux : b = a * (start / a) + a := by
      dsimp [b, r]
      omega
    calc
      b = a * (start / a) + a := haux
      _ = a * (start / a + 1) := by ring
  refine ⟨b, ?_, ?_⟩
  · simp only [window, Finset.mem_Icc]
    constructor
    · dsimp [b]
      omega
    · dsimp [b]
      omega
  · exact ⟨start / a + 1, hbdiv⟩

/-- Erdős Problem 709 holds for a singleton input: the multiplier `1` suffices. -/
@[category textbook, AMS 5 11]
theorem erdos_709.variants.singleton : Works 1 1 := by
  intro A M hcard hM hbound htwo start
  have hA : A = {M} := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hMz : M = z := Finset.mem_singleton.mp (hz ▸ hM)
    simpa [hMz] using hz
  obtain ⟨b, hb, hd⟩ :=
    exists_multiple_in_window M M start (by have := htwo M hM; omega) le_rfl
  refine ⟨fun _ => b, ?_, ?_⟩
  · intro u hu v hv _
    rw [hA] at hu hv
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
    exact hu.trans hv.symm
  · intro a ha
    rw [hA] at ha
    have hEq : a = M := Finset.mem_singleton.mp ha
    subst a
    simpa using And.intro hb hd

/-- For singleton inputs, every multiplier at least `1` works. -/
@[category API, AMS 5 11]
theorem works_one_of_one_le (k : ℕ) (hk : 1 ≤ k) : Works 1 k :=
  works_mono 1 1 k hk erdos_709.variants.singleton

/-- `IsAdmissible n c` says that for every set $A \subseteq [2,\infty)$ of $n$ natural numbers,
every block of at least $c \max(A)$ consecutive positive integers contains distinct multiples of
the elements of $A$. Restricting to positive integers loses nothing: translating a block by a
multiple of $\operatorname{lcm}(A)$ does not change which of its elements each $a \in A$ divides.
`Works` above is the same condition with an integer multiplier. -/
def IsAdmissible (n : ℕ) (c : ℝ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ start length : ℕ, c * ((A.sup id : ℕ) : ℝ) ≤ (length : ℝ) →
      HasDistinctMultiples A start length

/-- $f(n)$ is the infimum of the admissible $c$. Since $c\max(A)$ need not be an integer, "an
interval of $c\max(A)$ consecutive integers" is read as "at least $c\max(A)$ consecutive
integers" (a longer interval contains a shorter one). For $n \geq 1$ the set of admissible $c$
contains $n$ and is bounded below by $0$, so `sInf` is the true infimum. The value $f(0)=0$ is
a junk value and plays no role. -/
noncomputable def f (n : ℕ) : ℝ := sInf {c : ℝ | IsAdmissible n c}

/-- The integers $5, 6, 7$ contain no distinct multiples of $2$ and $3$, since $6$ is the only
multiple of each. So three consecutive integers are not enough for $A=\{2,3\}$. -/
@[category test, AMS 11]
theorem not_hasDistinctMultiples_two_three : ¬ HasDistinctMultiples {2, 3} 4 3 := by
  rintro ⟨x, hinj, h⟩
  obtain ⟨h2w, h2d⟩ := h 2 (by simp)
  obtain ⟨h3w, h3d⟩ := h 3 (by simp)
  simp only [window, Finset.mem_Icc] at h2w h3w
  have h23 : x 2 = x 3 := by omega
  have := hinj (by simp) (by simp) h23
  omega

def erdos_709.answer : ℕ → ℝ := sorry

/--
Let $f(n)$ be minimal such that, for any $A=\{a_1,\ldots,a_n\}\subseteq [2,\infty)\cap\mathbb{N}$
of size $n$, in any interval $I$ of $f(n)\max(A)$ consecutive integers there exist distinct
$x_1,\ldots,x_n\in I$ such that $a_i\mid x_i$.

Obtain good bounds for $f(n)$, or even an asymptotic formula.

We read "good bounds" as determining the order of magnitude of $f(n)$.
-/
@[category research open, question value, AMS 11]
theorem erdos_709 : f =Θ[atTop] erdos_709.answer := by
  sorry

/--
A problem of Erdős and Surányi [ErSu59], who proved
$$(\log n)^c \ll f(n) \ll n^{1/2}$$
for some constant $c>0$.

This is the lower bound.
-/
@[category research solved, AMS 11]
theorem erdos_709.variants.ersu_lower :
    ∃ c > (0 : ℝ), (fun n : ℕ ↦ Real.log n ^ c) =O[atTop] f := by
  sorry

/--
A problem of Erdős and Surányi [ErSu59], who proved
$$(\log n)^c \ll f(n) \ll n^{1/2}$$
for some constant $c>0$.

This is the upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_709.variants.ersu_upper :
    f =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/--
The lower bound here can be improved, using van Doorn's lower bound for [711] from [vD26], to
$$\frac{\log n}{\log\log n}\ll f(n).$$
-/
@[category research solved, AMS 11]
theorem erdos_709.variants.van_doorn_lower :
    (fun n : ℕ ↦ Real.log n / Real.log (Real.log n)) =O[atTop] f := by
  sorry

end Erdos709

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
- [ErSu59] Erdős, P. and Surányi, J., *Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs*. Mat. Lapok 10 (1959), 39-48. [PDF](https://www.renyi.hu/~p_erdos/1959-07.pdf)
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*.
  Hardy-Ramanujan J. 15 (1992), 34-50.
- [vD26] van Doorn, W., *On the length of an interval that contains distinct multiples of the
  first $n$ positive integers*. Integers 26 (2026), #A7.
  [arXiv:2601.16972](https://arxiv.org/abs/2601.16972)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos709

/-- There are distinct integers $x_a$ ($a \in A$) in the interval $[m, m+L)$ of $L$ consecutive
integers such that $a \mid x_a$ for all $a \in A$. -/
def HasDistinctMultiples (A : Finset ℕ) (m : ℤ) (L : ℕ) : Prop :=
  ∃ x : ℕ → ℤ, Set.InjOn x (A : Set ℕ) ∧ ∀ a ∈ A, m ≤ x a ∧ x a < m + L ∧ (a : ℤ) ∣ x a

/-- `IsAdmissible n c` says that for every set $A \subseteq [2,\infty)$ of $n$ natural numbers,
every interval of at least $c \max(A)$ consecutive integers contains distinct multiples of the
elements of $A$. -/
def IsAdmissible (n : ℕ) (c : ℝ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ (m : ℤ) (L : ℕ), c * ((A.sup id : ℕ) : ℝ) ≤ (L : ℝ) → HasDistinctMultiples A m L

/-- $f(n)$ is the infimum of the admissible $c$. Since $c\max(A)$ need not be an integer, "an
interval of $c\max(A)$ consecutive integers" is read as "at least $c\max(A)$ consecutive
integers" (a longer interval contains a shorter one). For $n \geq 1$ the set of admissible $c$
contains $n$ and is bounded below by $0$, so `sInf` is the true infimum. The value $f(0)=0$ is
a junk value and plays no role. -/
noncomputable def f (n : ℕ) : ℝ := sInf {c : ℝ | IsAdmissible n c}

/-- The integers $5, 6, 7$ contain no distinct multiples of $2$ and $3$, since $6$ is the only
multiple of each. So three consecutive integers are not enough for $A=\{2,3\}$. -/
@[category test, AMS 11]
theorem not_hasDistinctMultiples_two_three : ¬ HasDistinctMultiples {2, 3} 5 3 := by
  rintro ⟨x, hinj, h⟩
  obtain ⟨h2l, h2u, h2d⟩ := h 2 (by simp)
  obtain ⟨h3l, h3u, h3d⟩ := h 3 (by simp)
  have h23 : x 2 = x 3 := by
    push_cast at h2u h2d h3u h3d
    omega
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

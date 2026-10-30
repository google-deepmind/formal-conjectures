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
public import FormalConjectures.ErdosProblems.«675»

/-!
# Erdős Problem 240

*References:*
- [erdosproblems.com/240](https://www.erdosproblems.com/240)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
  [PDF](https://www.renyi.hu/~p_erdos/1965-17.pdf)
- [Po18] Pólya, Georg, *Zur arithmetischen Untersuchung der Polynome*. Math. Z. (1918), 143-148.
- [Ti73] Tijdeman, R., *On integers with many small prime factors*. Compositio Math. 26 (1973),
  319-330. [numdam](https://www.numdam.org/item/CM_1973__26_3_319_0/)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos240

/-- `a P i` is the `i`-th smallest element of `Erdos675.composedOf P`, the positive integers all
of whose prime factors lie in `P`, counting from index `0`. So `a P 0 = 1` (the site writes
$a_1<a_2<\cdots$).

For a nonempty set `P` of primes, `composedOf P` is infinite, `a P` is strictly increasing and the
natural-number subtractions below are exact. If `P` contains no prime, then `composedOf P = {1}`
and `a P i = 0` for `i ≥ 1` (the junk value of `Nat.nth`); the statements below exclude this. -/
noncomputable def a (P : Set ℕ) (i : ℕ) : ℕ :=
  Nat.nth (· ∈ Erdos675.composedOf P) i

set_option linter.style.formal_proof_palomar false in
/--
Is there an infinite set of primes $P$ such that if $\{a_1<a_2<\cdots\}$ is the set of integers
divisible only by primes in $P$ then $\lim a_{i+1}-a_i=\infty$?

The answer is yes, proved by Tijdeman [Ti73, Theorem 7]. The question was asked to Erdős by
Wintner [Er65b, p. 218]. See also Erdős Problem 368.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos240.lean#L1817"]
theorem erdos_240 :
    ∃ P : Set ℕ, P.Infinite ∧ P ⊆ {p : ℕ | p.Prime} ∧
      Tendsto (fun i ↦ a P (i + 1) - a P i) atTop atTop := by
  sorry

/--
Tijdeman [Ti73] resolved this question, proving that, for any $\epsilon>0$, there exists an
infinite set of primes $P$ such that, with $a_i$ defined as above,
$$a_{i+1}-a_i \gg a_i^{1-\epsilon}.$$
([Ti73, Theorem 7] is stated for $0<\epsilon<1$; for $\epsilon\geq 1$ the bound is trivial.)
-/
@[category research solved, AMS 11]
theorem erdos_240.variants.tijdeman_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Set ℕ, P.Infinite ∧ P ⊆ {p : ℕ | p.Prime} ∧
      (fun i ↦ (a P i : ℝ) ^ (1 - ε)) =O[atTop] (fun i ↦ ((a P (i + 1) - a P i : ℕ) : ℝ)) := by
  sorry

/--
The limit is infinite for a finite set of primes, which follows from a theorem of Pólya [Po18],
that if $f(n)$ is a quadratic integer polynomial without repeated roots then as
$n\to \infty$ the largest prime factor of $f(n)$ also approaches infinity.
Erdős [Er65b, p. 218] also credits this to Pólya.

Here $P$ is nonempty: for $P=\emptyset$ the set of integers is $\{1\}$ and there are no gaps.
-/
@[category research solved, AMS 11]
theorem erdos_240.variants.finite {P : Set ℕ} (hP : P.Finite) (hne : P.Nonempty)
    (hpr : P ⊆ {p : ℕ | p.Prime}) :
    Tendsto (fun i ↦ a P (i + 1) - a P i) atTop atTop := by
  sorry

/--
Tijdeman [Ti73] proved that, if $P$ is a finite set of primes, then
$$a_{i+1}-a_i \gg \frac{a_i}{(\log a_i)^C}$$
for some constant $C>0$ depending on $P$.

[Ti73, Theorem 1 and its Corollary] state this for the integers composed of all primes at most
$p$; it follows for every finite set of primes, since a subset of these integers has larger gaps.
-/
@[category research solved, AMS 11]
theorem erdos_240.variants.tijdeman_finite {P : Set ℕ} (hP : P.Finite) (hne : P.Nonempty)
    (hpr : P ⊆ {p : ℕ | p.Prime}) :
    ∃ C : ℝ, 0 < C ∧
      (fun i ↦ (a P i : ℝ) / Real.log (a P i : ℝ) ^ C) =O[atTop]
        (fun i ↦ ((a P (i + 1) - a P i : ℕ) : ℝ)) := by
  sorry

end Erdos240

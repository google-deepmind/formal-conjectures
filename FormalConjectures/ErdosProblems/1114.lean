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
# Erdős Problem 1114

*References:*
- [erdosproblems.com/1114](https://www.erdosproblems.com/1114)
- [Ba60b] Bálint, Elemér, *Proof of a conjecture of P. Erdős* (Hungarian: *Erdős Pál egy
  sejtésének bizonyítása*). Mat. Lapok 11 (1960), 33-40.
- [Lo76] Lorch, L., *Some monotonicity properties of polynomials with equally spaced zeros*.
  Acta Math. Acad. Sci. Hungar. 27 (1976), 293-300.
-/

@[expose] public section

open scoped Polynomial

namespace Erdos1114

/-- `RightGapMonotone N b` is about the points `b 0 < b 1 < ⋯ < b (N - 1)` (the zeros of the
derivative). The gaps `b (i + 1) - b i` do not decrease as `i` increases through the right half:
for all `i` with `N ≤ 2 * (i + 1)` such that the next gap `b (i + 2) - b (i + 1)` exists. The
first such gap is the middle one, centred at the midpoint, when `N` is even, and the gap
starting at the midpoint `b ((N - 1) / 2)` when `N` is odd. -/
def RightGapMonotone (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 2 < N → N ≤ 2 * (i + 1) →
    b (i + 1) - b i ≤ b (i + 2) - b (i + 1)

/-- `GapSymmetric N b` says that the sequence of gaps of `b 0, …, b (N - 1)` is a palindrome:
the gap `b (i + 1) - b i` equals its mirror image `b (N - 1 - i) - b (N - 2 - i)`. Together with
`RightGapMonotone` this says that the gaps do not decrease from the midpoint towards either
endpoint. -/
def GapSymmetric (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i + 1 < N →
    b (i + 1) - b i = b (N - 1 - i) - b (N - 2 - i)

/--
Let $f(x)\in \mathbb{R}[x]$ be a polynomial of degree $n$ whose roots $\{a_0<\cdots<a_n\}$ are
all real and form an arithmetic progression.

The differences between consecutive zeros of $f'(x)$, beginning from the midpoint of $(a_0,a_n)$
towards the endpoints, are monotonically increasing.

Proved by Bálint [Ba60b]; some generalisations were given by Lorch [Lo76]. We take $f$ of
degree $N+1$ with the $N+1$ roots $a+jd$ ($0\le j\le N$, $d>0$), since the number of roots must
equal the degree, and read "increasing" as non-decreasing. Here `b k` is the zero of $f'$ in
$(a+kd,a+(k+1)d)$, which exists and is the only zero there by Rolle's theorem (see
`erdos_1114.variants.rolle`).
-/
@[category research solved, AMS 12 26, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1114.lean#L1606"]
theorem erdos_1114 {N : ℕ} (hN : 0 < N) {a d : ℝ} (hd : 0 < d) {f : ℝ[X]} {b : ℕ → ℝ}
    (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j : ℕ, j ≤ N → f.eval (a + d * j) = 0)
    (hb : ∀ k : ℕ, k < N → b k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)))
    (hderiv : ∀ k : ℕ, k < N → f.derivative.eval (b k) = 0) :
    RightGapMonotone N b ∧ GapSymmetric N b := by
  sorry

/--
All the zeros of $f'(x)$ are all distinct real numbers in $(a_0,a_n)$ by Rolle's theorem.

Precisely, for $f$ as in `erdos_1114` (degree $N+1$, roots $a+jd$ for $0\le j\le N$), each
interval $(a+kd,a+(k+1)d)$ with $k<N$ contains exactly one zero of $f'$, and every zero of $f'$
lies in one of these intervals.
-/
@[category textbook, AMS 12 26]
theorem erdos_1114.variants.rolle {N : ℕ} {a d : ℝ} (hd : 0 < d) {f : ℝ[X]}
    (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j : ℕ, j ≤ N → f.eval (a + d * j) = 0) :
    (∀ k : ℕ, k < N →
      ∃! x : ℝ, x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)) ∧ f.derivative.eval x = 0) ∧
    (∀ x : ℝ, f.derivative.eval x = 0 →
      ∃ k : ℕ, k < N ∧ x ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) := by
  sorry

end Erdos1114

/-
Copyright 2025 The Formal Conjectures Authors.

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
# Collatz conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
* [erdosproblems.com/1135](https://www.erdosproblems.com/1135)
* [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
* [La10] Lagarias, Jeffrey C., The {$3x+1$} problem: an overview. (2010), 3--29.
* [La16] Lagarias, Jeffrey C., Erdős, Klarner, and the {$3x+1$} problem. Amer. Math. Monthly
  (2016), 753--776.
* [La85] Lagarias, Jeffrey C., The {$3x+1$} problem and its generalizations. Amer. Math. Monthly
  (1985), 3--23.
* [Ba25] Bařina, David, Improved verification limit for the convergence of the Collatz
  conjecture. J. Supercomput. **81** (2025), 810.
  [DOI](https://doi.org/10.1007/s11227-025-07337-0)
* [El93] Eliahou, Shalom, The {$3x+1$} problem: new lower bounds on nontrivial cycle lengths.
  Discrete Math. **118** (1993), 45--56.
* [He23] Hercher, Christian, There are no Collatz $m$-cycles with $m \le 91$. J. Integer Seq.
  **26** (2023), Article 23.3.5.
* [Rh87] Rhin, Georges, Approximants de Padé et mesures d'irrationalité de $\log 2$, $\log 3$ et
  $\log(2/3)$. Séminaire de Théorie des Nombres, Paris 1985–86, Progr. Math. **71**, Birkhäuser
  (1987), 153--164.
* [Wa26] Wang, Xinjun, Non-existence of Collatz $m$-cycles for $m \le 95$. Zenodo (2026).
  [DOI](https://doi.org/10.5281/zenodo.21017296)
-/

@[expose] public section

namespace CollatzConjecture

/--
Consider the following operation on the natural numbers:
If the number is even, divide it by two.
If the number is odd, triple it and add one.
-/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/--
Now form a sequence beginning with any positive integer, where each subsequent term is obtained
by applying the operation defined above to the previous term.
The **Collatz conjecture** states that for any positive integer $n$, there exists a natural number
$m$ such that the $m$-th term of the sequence is 1.
-/
@[category research open, AMS 11 37]
theorem collatz_conjecture (n : ℕ) (hn : n > 0) : ∃ m, collatzStep^[m] n = 1 := by
  sorry

/--
Bařina (2025) [Ba25] computationally verified that every positive integer $n \le 2^{71}$
eventually reaches $1$ under iteration of `collatzStep`.
-/
@[category research solved, AMS 11 37]
theorem collatz_conjecture_of_le_two_pow_71 (n : ℕ) (hn : 0 < n) (hle : n ≤ 2 ^ 71) :
    ∃ k : ℕ, (collatzStep^[k]) n = 1 := by
  sorry

/--
Conditional on Bařina's $2^{71}$ verification, every positive integer $n > 0$ whose trajectory
has not yet reached $1$ passes through some iterate strictly exceeding $2^{71}$.
-/
@[category research solved, AMS 11 37]
theorem two_pow_71_lt_iterate
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, (collatzStep^[s]) k = 1)
    {n : ℕ} (hn : 0 < n) (h1 : ∀ s, (collatzStep^[s]) n ≠ 1) :
    ∃ t, 2 ^ 71 < (collatzStep^[t]) n := by
  by_contra! h
  obtain ⟨s, hs⟩ := hB n hn (h 0)
  exact h1 s hs

/--
The shortcut Collatz map $T(n)$, sending even $n$ to $n / 2$ and odd $n$ to $(3n + 1) / 2$.
-/
def collatzShortcut (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

/--
Eliahou (1993) [El93] and Bařina (2025) [Ba25]: any non-trivial cycle of the shortcut Collatz
map `collatzShortcut` has period at least $217976794617$ (applying Eliahou's continued-fraction
method at Bařina's $2^{71}$ verification bound).
-/
@[category research solved, AMS 11 37]
theorem le_period_collatzShortcut (n : ℕ) (hn : 2 < n) (p : ℕ) (hp : 0 < p)
    (hcycle : (collatzShortcut^[p]) n = n) : 217976794617 ≤ p := by
  sorry

/--
A positive integer $n$ lies on a Collatz $m$-cycle if the orbit of $n$ under `collatzShortcut` is
periodic with some positive period $p$ containing $p$ distinct elements and exactly $m$ local minima.
-/
def IsMCycle (m n : ℕ) : Prop :=
  0 < n ∧ ∃ p > 0, collatzShortcut^[p] n = n ∧
    ((List.range p).map (collatzShortcut^[·] n)).Nodup ∧
    ((Finset.range p).filter fun i =>
      collatzShortcut^[i + 1] n < collatzShortcut^[i] n ∧
      collatzShortcut^[i + 1] n < collatzShortcut^[i + 2] n).card = m

/-- Every point on a Collatz $m$-cycle is strictly positive. -/
@[category API, AMS 11 37]
theorem IsMCycle.ne_zero {m n : ℕ} (h : IsMCycle m n) : n ≠ 0 :=
  ne_of_gt h.1

/-- The trivial cycle $1 \to 2 \to 1$ is a $1$-cycle through $1$. -/
@[category test, AMS 11 37]
theorem isMCycle_one_one : IsMCycle 1 1 := ⟨by decide, 2, by decide⟩

/-- The trivial cycle $1 \to 2 \to 1$ is a $1$-cycle through $2$. -/
@[category test, AMS 11 37]
theorem isMCycle_one_two : IsMCycle 1 2 := ⟨by decide, 2, by decide⟩

/--
Effective linear-form bound for $\log_2 3$ proved from Mathlib alone in the linked development,
replacing Rhin's (1987) [Rh87] effective irrationality measure in the Collatz $m$-cycle argument:
for $K \ge 2438425051595107335801557824$, the linear form $(K + L)\log 2 - K\log 3$ cannot lie
strictly between $0$ and $100 \cdot 2^{1 - K / 2^{68}}$.
-/
@[category research solved, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem diophantine_terminal (K L : ℕ) (hK : 2438425051595107335801557824 ≤ K)
    (h0 : 0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3)
    (h1 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 <
      100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68)) :
    False := by
  sorry

/--
Hercher (2023) [He23]: conditional on Bařina's $2^{71}$ verification, there is no non-trivial
Collatz $m$-cycle with $m \le 91$. (The extension through $m \le 100$ is formalized in the linked
repository using `native_decide` for $92 \le m \le 100$.)
-/
@[category research solved, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem not_isMCycle_of_le_91_of_barina
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, (collatzStep^[s]) k = 1)
    (m : ℕ) (hm : m ≤ 91) (n : ℕ) (hn : 2 < n) :
    ¬ IsMCycle m n := by
  sorry

/--
It is open whether a non-trivial Collatz $101$-cycle exists (for $m \le 95$, see Wang (2026) [Wa26];
for $m \le 100$, a certificate and Lean 4 formalization using `native_decide` for $92 \le m \le 100$
are given in the repository linked at `PALOMAR-2026-11-15-000008`).
-/
@[category research open, AMS 11 37]
theorem not_isMCycle_101 (n : ℕ) (hn : 2 < n) : ¬ IsMCycle 101 n := by
  sorry

/--
The cycle-free half of the Collatz conjecture: there are no non-trivial Collatz $m$-cycles for any
$m \ge 1$.
-/
@[category research open, AMS 11 37]
theorem no_nontrivial_collatz_cycles (m n : ℕ) (hn : 2 < n) : ¬ IsMCycle m n := by
  sorry

end CollatzConjecture

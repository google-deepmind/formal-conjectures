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
# Collatz conjecture and $m$-cycles

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
- [Ba25] D. Bařina, *Improved verification limit for the convergence of the Collatz conjecture*,
  The Journal of Supercomputing **81** (2025), 810.
  [DOI](https://doi.org/10.1007/s11227-025-07337-0)
- [He23] C. Hercher, *There are no Collatz $m$-cycles with $m \le 91$*,
  Journal of Integer Sequences **26** (2023), Article 23.3.5.
- [Rh87] G. Rhin, *Approximants de Padé et mesures d'irrationalité de $\log 2$, $\log 3$ et
  $\log(2/3)$*, Séminaire de Théorie des Nombres, Paris 1985–86, Progress in Mathematics **71**,
  Birkhäuser (1987), 153–164.
- [Wa26] X. Wang, *Non-existence of Collatz $m$-cycles for $m \le 95$*, Zenodo (2026).
  [DOI](https://doi.org/10.5281/zenodo.21017296)
-/

@[expose] public section

namespace CollatzConjecture

/--
Single step of the Collatz map on `ℕ`.
For $n > 0$, even numbers map to $n / 2$ and odd numbers map to $3n + 1$.
-/
def collatzStep (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if Even n then n / 2
  else 3 * n + 1

/--
The **Collatz conjecture** states that repeating two arithmetic operations will eventually
transform every positive integer into $1$.
-/
@[category research open, AMS 11 37]
theorem collatz_conjecture (n : ℕ) (hn : 0 < n) : ∃ k : ℕ, (collatzStep^[k]) n = 1 := by
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
has not yet reached $1$ after $s$ steps passes through some iterate strictly exceeding $2^{71}$.
-/
@[category research solved, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem two_pow_71_lt_iterate
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, (collatzStep^[s]) k = 1)
    {n : ℕ} (hn : 0 < n) (h1 : ∀ s, (collatzStep^[s]) n ≠ 1) :
    ∃ t, 2 ^ 71 < (collatzStep^[t]) n := by
  sorry

/--
The shortcut Collatz map $T(n)$, sending even $n$ to $n / 2$ and odd $n$ to $(3n + 1) / 2$.
-/
def collatzShortcut (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

/--
Any non-trivial cycle of the shortcut Collatz map `collatzShortcut` has period at least
$217976794617$.
-/
@[category research open, AMS 11 37]
theorem le_period_collatzShortcut (n : ℕ) (hn : 2 < n) (p : ℕ) (hp : 0 < p)
    (hcycle : (collatzShortcut^[p]) n = n) : 217976794617 ≤ p := by
  sorry

/--
A positive integer $n$ lies on a Collatz $m$-cycle if the orbit of $n$ under `collatzStep` is
periodic with some positive period $p$ containing $m$ local minima, meaning there exists a strictly
increasing sequence of step indices $0 = t_0 < t_1 < \dots < t_m = p$ such that for each
$i < m$, starting from $x_i = \text{collatzStep}^{[t_i]}(n)$, the trajectory rises through odd
steps of `collatzShortcut` (`collatzStep` followed by division by $2$) for $k_i \ge 1$ steps and
then falls through division by $2$ for $l_i \ge 1$ steps until reaching $x_{i+1}$.
-/
def IsMCycle (m : ℕ) (n : ℕ) : Prop :=
  0 < m ∧ ∃ p > 0, (collatzStep^[p]) n = n ∧
    ∃ (t : Fin (m + 1) → ℕ),
      t 0 = 0 ∧ t (Fin.last m) = p ∧ StrictMono t ∧
      ∀ i : Fin m,
        let a := t i.castSucc
        let b := t i.succ
        ∃ c, a < c ∧ c < b ∧
          (∀ s, a ≤ s → s < c →
            Odd ((collatzStep^[s]) n) ∧ (collatzStep^[s + 1]) n < (collatzStep^[s + 2]) n) ∧
          (∀ s, c ≤ s → s < b → Even ((collatzStep^[s]) n)) ∧
          Odd ((collatzStep^[b]) n)

/-- Every point on a Collatz $m$-cycle is strictly positive. -/
@[category API, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem IsMCycle.ne_zero {m n : ℕ} (h : IsMCycle m n) : n ≠ 0 := by
  sorry

/-- The trivial cycle $1 \to 4 \to 2 \to 1$ is a $1$-cycle starting at $1$. -/
@[category test, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem isMCycle_one_one : IsMCycle 1 1 := by
  sorry

/-- The trivial cycle $2 \to 1 \to 4 \to 2$ is a $1$-cycle starting at $2$. -/
@[category test, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem isMCycle_one_two : IsMCycle 1 2 := by
  sorry

/--
Effective irrationality measure for $\log_2 3$ via Rhin's (1987) [Rh87] Padé approximants:
there is no positive integer solution $(K, L)$ with $K \ge 135147$ to the Diophantine inequality
$0 < 2^L - 3^K$ and $(2^L - 3^K) \cdot K^{14} < 3^K$.
-/
@[category research solved, AMS 11 37,
  formal_proof using lean4 at "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-15-000008"]
theorem diophantine_terminal (K L : ℕ) (hK : 135147 ≤ K) :
    ¬(0 < (2 : ℤ) ^ L - (3 : ℤ) ^ K ∧
      ((2 : ℤ) ^ L - (3 : ℤ) ^ K) * (K : ℤ) ^ 14 < (3 : ℤ) ^ K) := by
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

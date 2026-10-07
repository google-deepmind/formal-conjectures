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
# Erdős Problem 129

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)
-/

@[expose] public section

open Finset

namespace Erdos129

/-- Under the edge colouring `c` of $K_N$, every edge inside the vertex set `T` has colour `i`,
i.e. `T` spans a monochromatic clique of colour `i`. -/
def IsMonoClique {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (i : Fin r) (T : Finset (Fin N)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c s(x, y) = i

/-- `N` has the Ramsey property for `(n, k, r)`: for every `r`-colouring of the edges of $K_N$
there is a set `S` of `n` vertices and a colour `i` such that `S` contains no $K_k$ all of whose
edges have colour `i`. -/
def HasRamseyProperty (n k r N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin r, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ i : Fin r, ∀ T ⊆ S, T.card = k → ¬ IsMonoClique c i T

/-- $R(n; k, r)$: the smallest `N` with the Ramsey property for `(n, k, r)`. -/
noncomputable def R (n k r : ℕ) : ℕ := sInf {N | HasRamseyProperty n k r N}

/-- Exponential lower bound (Girao): $2 ^ {\lfloor n / 100 \rfloor} < R(n; 3, 2)$ for all
$n \ge 100$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-129-lean/blob/06e2f9ba62d7511e3d9ccfd96dcada975b6bd9e1/Erdos129.lean"]
theorem two_pow_lt_R (n : ℕ) (hn : 100 ≤ n) : 2 ^ (n / 100) < R n 3 2 := by
  sorry

/-- Even the "for all sufficiently large $n$" version of the bound fails for two colours:
for no $C \ge 0$ does $R(n; 3, 2) < C ^ {\sqrt{n}}$ hold eventually. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-129-lean/blob/06e2f9ba62d7511e3d9ccfd96dcada975b6bd9e1/Erdos129.lean"]
theorem not_eventually_R_lt (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, (R n 3 2 : ℝ) < C ^ Real.sqrt n := by
  sorry

/--
Let $R(n;k,r)$ be the smallest $N$ such that if the edges of $K_N$ are $r$-coloured then there is
a set of $n$ vertices which does not contain a copy of $K_k$ in at least one of the $r$ colours.
Prove that there is a constant $C=C(r)>1$ such that $R(n;3,r) < C^{\sqrt{n}}$.

Antonio Girao has pointed out that this problem as written is easily disproved, and
indeed $R(n;3,2) \geq C^{n}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-129-lean/blob/06e2f9ba62d7511e3d9ccfd96dcada975b6bd9e1/Erdos129.lean"]
theorem erdos_129 : answer(False) ↔
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  sorry

end Erdos129

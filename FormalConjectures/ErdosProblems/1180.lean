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
# Erdős Problem 1180

*References:*
- [erdosproblems.com/1180](https://www.erdosproblems.com/1180)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Sh02] Shparlinski, Igor E., *On a question of Erdős and Graham*. Arch. Math. (Basel) (2002),
  445-448.
- [Gl06] Glibichuk, A. A., *Combinatorial properties of sets of residues modulo a prime and the
  Erdős-Graham problem*. Mat. Zametki (2006), 384-395.
-/

@[expose] public section

open Filter

namespace Erdos1180

/--
`Represents ε p a s` says that the multiset `s` of denominators `n` with `1 ≤ n ≤ p^ε` and
`n` coprime to `p` has `∑ n⁻¹ = a` in `ZMod p`.
-/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

/--
`C ε` is the least `C` such that, for all primes `p`, every residue modulo `p` is the sum of at
most `C` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}` (or `0` if no such `C` exists).
-/
noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/--
Let $\epsilon>0$. Does there exist a constant $C_\epsilon$ such that, for all primes $p$, every
residue modulo $p$ is the sum of at most $C_\epsilon$ many elements of
$$\{ n^{-1} : 1\leq n\leq p^\epsilon\}$$
where $n^{-1}$ denotes the inverse of $n$ modulo $p$?

The original question was answered in the affirmative, with $C_\epsilon \ll \epsilon^{-3}$, by
Shparlinski [Sh02]. This was improved to $\ll \epsilon^{-2}$ by Glibichuk [Gl06]. It is trivial
that at least $\gg \epsilon^{-1}$ summands are required, and it may be that
$C_\epsilon\leq \epsilon^{-1-o(1)}$ is possible.

See also [540](https://www.erdosproblems.com/540).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1180.lean#L1249"]
theorem erdos_1180 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s := by
  sorry

/-- Shparlinski [Sh02] proved that $C_\epsilon \ll \epsilon^{-3}$. -/
@[category research solved, AMS 11]
theorem erdos_1180.variants.shparlinski : ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    (C ε : ℝ) ≤ K * ε⁻¹ ^ 3 := by
  sorry

/-- Glibichuk [Gl06] proved that $C_\epsilon \ll \epsilon^{-2}$. -/
@[category research solved, AMS 11]
theorem erdos_1180.variants.glibichuk : ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    (C ε : ℝ) ≤ K * ε⁻¹ ^ 2 := by
  sorry

/-- It is trivial that at least $\gg \epsilon^{-1}$ summands are required. -/
@[category research solved, AMS 11]
theorem erdos_1180.variants.lower_bound : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    K * ε⁻¹ ≤ C ε := by
  sorry

/-- Is $C_\epsilon\leq \epsilon^{-1-o(1)}$? -/
@[category research open, AMS 11]
theorem erdos_1180.variants.optimal : answer(sorry) ↔ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ) := by
  sorry

end Erdos1180

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
# Passive-Output Catalytic Register Programs (`arXiv:2609.18692`)

Formalization of open questions from Section 6 of Antoine Vinciguerra's operator analysis of
passive-output catalytic register programs (`RP^{pass}_K(r, t)`), together with the
positive-characteristic two-register digit-sum characterization proved in Lean 4 and registered
on Palomar (`PALOMAR-2026-11-26-000004`).

In a passive-output `r`-register program over a commutative ring `R`, register `0` is the
output register `O` (written to via additive updates `O ← O + p(R_1, ..., R_{r-1}, x)` and
never read on the right-hand side of any instruction), while registers `1, ..., r - 1` are
catalytic work registers that must be restored identically to their initial values at program
termination. An instruction that depends on the input `x` counts as one input access.

*References:*
- Antoine Vinciguerra, *An Operator Approach to Register Programs for Catalytic Computing*,
  [arXiv:2609.18692](https://arxiv.org/abs/2609.18692) (2026), Definition 2.2, Theorem 3.5,
  Section 6.
- Alexander S. Donahue, *Prime-Field Digit-Sum Dichotomy and Improved Three-Register Powering
  Exponents in Passive Catalytic Register Programs*,
  [Zenodo 10.5281/zenodo.24517198](https://doi.org/10.5281/zenodo.24517198) ·
  [Palomar PALOMAR-2026-11-26-000004](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000004).
-/

@[expose] public section

namespace Arxiv.«2609.18692»

/-- Instructions of a two-register passive-output catalytic register program `(O, U)` with
coefficients in `ℤ` (reduced modulo `p` over `ZMod p` or cast into any commutative ring `R`).
`addU c` performs `U ← U + c`; `addUX c` performs `U ← U + c * x` (one input access);
`addOPow k c` performs `O ← O + c * U^k` (no input access). -/
inductive Pass2Instr where
  | addU (c : ℤ)
  | addUX (c : ℤ)
  | addOPow (k : ℕ) (c : ℤ)
  deriving DecidableEq, Repr

/-- Number of input accesses (`addUX` instructions) in a two-register passive program. -/
def Pass2Instr.accesses : List Pass2Instr → ℕ
  | [] => 0
  | .addUX _ :: rest => 1 + accesses rest
  | _ :: rest => accesses rest

/-- Execute a two-register passive program on `(O, U)` with input `x` in any commutative ring `R`. -/
def Pass2Instr.exec {R : Type*} [CommRing R] (x : R) : List Pass2Instr → R × R → R × R
  | [], st => st
  | .addU c :: rest, (o, u) => exec x rest (o, u + c)
  | .addUX c :: rest, (o, u) => exec x rest (o, u + c * x)
  | .addOPow k c :: rest, (o, u) => exec x rest (o + c * u ^ k, u)

/-- A univariate polynomial `f ∈ 𝔽_p[x]` is cleanly computable in `RP^{pass}_{𝔽_p}(2, t)`
under formal-polynomial cleanliness if there is a program with at most `t` input accesses
whose literal execution cleanly computes `f` over every characteristic-`p` commutative ring. -/
def InRPPass2Formal (p t : ℕ) (f : Polynomial (ZMod p)) : Prop :=
  ∃ prog : List Pass2Instr, Pass2Instr.accesses prog ≤ t ∧
    ∀ (R : Type) [CommRing R] [CharP R p] (o u x : R),
      Pass2Instr.exec x prog (o, u) =
        (o + f.eval₂ (ZMod.castHom (dvd_refl p) R) x, u)

/-- Base-`p` digit sum `s_p(d)`. -/
def basePDigitSum (p d : ℕ) : ℕ :=
  (Nat.digits p d).sum

/--
**Solved positive-characteristic variant (`PALOMAR-2026-11-26-000004`):**
For every prime `p`, every `t ≥ 1`, and every `f ∈ 𝔽_p[x]`, `f` is cleanly computable in
`RP^{pass}_{𝔽_p}(2, t)` (formal-polynomial cleanliness) if and only if every degree `d ≥ 2`
with nonzero `[x^d] f` satisfies `s_p(d) ≤ min (p - 1) (t - 1)`.
In particular, `x^(p^m)` is cleanly computable in only `2` input accesses for every `m`, showing
that Vinciguerra's characteristic-0 lower bounds do not extend to characteristic `p`.
-/
@[category research solved, AMS 11 12 68,
  formal_proof using lean4 at
    "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000004"]
theorem two_register_prime_field_digit_sum_dichotomy (p t : ℕ) (hp : p.Prime) (ht : 1 ≤ t)
    (f : Polynomial (ZMod p)) :
    InRPPass2Formal p t f ↔
      ∀ d : ℕ, 2 ≤ d → f.coeff d ≠ 0 → basePDigitSum p d ≤ min (p - 1) (t - 1) := by
  sorry

/-- Instructions of a three-register passive-output catalytic register program `(O, U, V)` over `ℚ`
with polynomial updates to `O` and linear-in-`x` / polynomial-in-other-register shear updates. -/
inductive Pass3Instr where
  | addU (c : ℚ)
  | addUX (c : ℚ)
  | addUPowV (k : ℕ) (c : ℚ)
  | addV (c : ℚ)
  | addVX (c : ℚ)
  | addVPowU (k : ℕ) (c : ℚ)
  | addOMon (a b : ℕ) (c : ℚ)
  deriving DecidableEq

/-- Number of input accesses in a three-register passive program. -/
def Pass3Instr.accesses : List Pass3Instr → ℕ
  | [] => 0
  | .addUX _ :: rest => 1 + accesses rest
  | .addVX _ :: rest => 1 + accesses rest
  | _ :: rest => accesses rest

/-- Execute a three-register passive program on `(O, U, V)` with input `x` over `ℚ[O, U, V, x]`. -/
def Pass3Instr.exec {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) :
    List Pass3Instr → R × R × R → R × R × R
  | [], st => st
  | .addU c :: rest, (o, u, v) => exec x rest (o, u + algebraMap ℚ R c, v)
  | .addUX c :: rest, (o, u, v) => exec x rest (o, u + algebraMap ℚ R c * x, v)
  | .addUPowV k c :: rest, (o, u, v) => exec x rest (o, u + algebraMap ℚ R c * v ^ k, v)
  | .addV c :: rest, (o, u, v) => exec x rest (o, u, v + algebraMap ℚ R c)
  | .addVX c :: rest, (o, u, v) => exec x rest (o, u, v + algebraMap ℚ R c * x)
  | .addVPowU k c :: rest, (o, u, v) => exec x rest (o, u, v + algebraMap ℚ R c * u ^ k)
  | .addOMon a b c :: rest, (o, u, v) =>
      exec x rest (o + algebraMap ℚ R c * u ^ a * v ^ b, u, v)

/-- Clean computability of `x^d` in `RP^{pass}_ℚ(3, t)` over all `ℚ`-algebras. -/
def PowerInRPPass3Q (t d : ℕ) : Prop :=
  ∃ prog : List Pass3Instr, Pass3Instr.accesses prog ≤ t ∧
    ∀ (R : Type) [CommRing R] [Algebra ℚ R] (o u v x : R),
      Pass3Instr.exec x prog (o, u, v) = (o + x ^ d, u, v)

/--
**Open Question (Vinciguerra `arXiv:2609.18692` §6 / Donahue 2026 §5):**
For every `t ≥ 5`, does there exist a three-register passive-output catalytic program over `ℚ`
with at most `t` input accesses cleanly computing `x^(2t - 3)`?
Confirmed explicitly in Lean 4 for `t = 5, 6, 7, 8, 9` (`x^7, x^9, x^11, x^13, x^15`) in
`PALOMAR-2026-11-26-000004`; open for all `t ≥ 10`.
-/
@[category research open, AMS 12 68]
theorem three_register_passive_powering_linear_frontier :
    ∀ t : ℕ, 5 ≤ t → PowerInRPPass3Q t (2 * t - 3) := by
  sorry

/--
**Open Question (Vinciguerra `arXiv:2609.18692` §6):**
Is the maximum degree of a monomial `x^d` cleanly computable in `RP^{pass}_ℚ(3, t)` bounded
linearly in `t` (specifically `d ≤ 2t - 3` for all `t ≥ 4`), or can three passive catalytic
registers achieve superlinear degree growth in `t`?
-/
@[category research open, AMS 12 68]
theorem three_register_passive_degree_upper_bound :
    ∀ t d : ℕ, 4 ≤ t → PowerInRPPass3Q t d → d ≤ 2 * t - 3 := by
  sorry

end Arxiv.«2609.18692»

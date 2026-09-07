# Ticket Board — Leopoldt's conjecture

## Summary
- Total: 8 tickets (5 content + 3 cleanup/submission)
- Open: 8 | In Progress: 0 | Done: 0
- Parallel capacity: 1 (single file, short chain)
- Plan: `.mathlib-quality/plan.md` · Decomposition: `.mathlib-quality/decomposition.md`

This is a **statement-only** contribution. Only `[T004]` carries a genuine proof obligation;
everything else is `sorry` by design (`FormalConjectures` sets `warn.sorry = false`).

---

### [T001] Definitions: `IsPrincipalUnitAbove` and `IsPadicRelation`
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: def
- **Mathlib check**: neither is in mathlib. `HeightOneSpectrum`, `adicCompletion`, `PadicInt.appr`
  all exist and are used directly. There is no `Module ℤ_[p]` on a pro-p group anywhere in
  mathlib (see AG1 in `decomposition.md`), which is why `IsPadicRelation` is phrased by limits.
- **Naming**: `IsFoo`-style predicates, `UpperCamelCase`, inside `namespace Leopoldt` (the
  `linter.style.namespace` linter is on for this library).

#### Statement
```lean
def IsPrincipalUnitAbove (u : (𝓞 K)ˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → (u : 𝓞 K) - 1 ∈ v.asIdeal

def IsPadicRelation (ε : Fin (rank K) → (𝓞 K)ˣ) (a : Fin (rank K) → ℤ_[p]) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal →
    Tendsto (fun n : ℕ ↦ ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.adicCompletion K))
      atTop (nhds 1)
```

#### Proof sketch
None — definitions. Both must elaborate; verified by `lake build`.

#### Mathlib lemmas needed
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion` — the completion `K_v`, a complete valued
  (hence topological) field, so `nhds` is meaningful.
- `PadicInt.appr` / `PadicInt.appr_spec` (`Mathlib/NumberTheory/Padics/RingHoms.lean:356, 405`) —
  the canonical integer approximation, `x - (x.appr n : ℤ_[p]) ∈ span {p ^ n}`.
- `NumberField.Units.rank` (`DirichletTheorem.lean:359`).

#### Sources
See L1 and L2 in `.mathlib-quality/decomposition.md` for the verbatim quotes from
Nelson (arXiv:1308.4637) §1, §3 and Lemma 4.2, and from Mihăilescu (arXiv:1105.4544) §1.

#### Generality decision
- `(p : ℕ) [Fact p.Prime]` to match mathlib's `ℤ_[p]`.
- Primes above `p` as `(p : 𝓞 K) ∈ v.asIdeal` rather than an `Ideal.LiesOver` instance, so the
  condition is a plain `Prop` and quantifies uniformly over `v`.
- `PadicInt.appr` rather than an existential over approximating sequences: `STATEMENTS.md` warns
  about existentials in hypotheses, and `appr` is canonical (choice-independence argued in L2).

---

### [T002] State `leopoldt_conjecture`
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: T001
- **Parallel**: no
- **Type**: theorem (`sorry`)

#### Statement
```lean
@[category research open, AMS 11]
theorem leopoldt_conjecture (ε : Fin (rank K) → (𝓞 K)ˣ) (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) :
    a = 0 := by
  sorry
```

#### Proof sketch
`sorry` — this is an open conjecture. The work is the docstring: it must state the rank
formulation in LaTeX (`$ $`, per `linter.style.latex_docstring`) and say why the Lean form is
equivalent to it.

#### Mathlib lemmas needed
- `NumberField.Units.IsMaxRank` (`Regulator.lean:71`) — the maximal-rank hypothesis.
- `NumberField.Units.isMaxRank_iff_closure_finiteIndex` (`Regulator.lean:108`) — cited in the
  docstring/decomposition as the bridge to "generates a finite-index subgroup".

#### Sources
L3 in `decomposition.md`: Nelson Conjecture 3.1 (p. 7), Gras et al. §1, Mihăilescu §1,
Wikipedia, NSW Theorem 10.3.6.

#### Generality decision
- No "odd `p`" hypothesis: NSW's caveat is an artefact of mapping into the full local units;
  see attack [4] on L3.
- `ε` universally quantified rather than fixed to `fundSystem K`: equivalent (all max-rank
  families are commensurable) and does not ask the reader to trust one choice.

---

### [T003] State `leopoldt_conjecture.variants.abelian` (Ax-Brumer)
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: T002
- **Parallel**: no
- **Type**: theorem (`sorry`)

#### Statement
```lean
@[category research solved, AMS 11]
theorem leopoldt_conjecture.variants.abelian [IsAbelianGalois ℚ K]
    (ε : Fin (rank K) → (𝓞 K)ˣ) (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) :
    a = 0 := by
  sorry
```

#### Proof sketch
`sorry` — solved in the literature, no formal proof exists, so no `@[formal_proof]` attribute.

#### Mathlib lemmas needed
- `IsAbelianGalois` (`Mathlib/FieldTheory/Galois/Abelian.lean:25`) — verified present.

#### Sources
L4 in `decomposition.md`: Nelson §1 p. 2 (verbatim), Wikipedia, Ax (1965), Brumer (1967).

#### Generality decision
Only the `ℚ` case is claimed, although Ax-Brumer also covers abelian extensions of imaginary
quadratic fields and CM fields with abelian maximal real subfield. Under-claiming is safe;
widening it is a possible follow-up but needs its own source check.

---

### [CLEANUP-1] Run `/cleanup` on `LeopoldtConjecture.lean`
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: T003
- **Parallel**: no
- **Type**: cleanup
- **Description**: Cadence rule (§1g): cleanup after the 3rd proof/definition ticket on this
  file. Check: copyright header, exactly one module docstring, `$ $` maths and
  `[label](url)` links in every docstring (`linter.style.latex_docstring`), every
  `@[category research …]` declaration has a docstring
  (`linter.style.category_docstring`), `AMS 11` present (`linter.style.ams_attribute`), all
  declarations namespaced, no unused `open`s, line length ≤ 100.

---

### [T004] Prove `exists_isMaxRank_isPrincipalUnitAbove`
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: CLEANUP-1
- **Parallel**: no
- **Type**: theorem (**real proof obligation — the only one in this project**)

#### Statement
```lean
@[category API]
theorem exists_isMaxRank_isPrincipalUnitAbove :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε ∧ ∀ i, IsPrincipalUnitAbove K p (ε i) := by
  sorry
```

#### Proof sketch
1. **Set `N := Nat.card ((𝓞 K) ⧸ Ideal.span {(p : 𝓞 K)})ˣ`.** The quotient is a finite ring
   (`𝓞 K` is ℤ-free of rank `[K : ℚ]` and `(p) ≠ 0` since `NumberField K` gives `CharZero`), so
   `N` is finite and `0 < N`.
2. **Take `ε i := fundSystem K i ^ N`** and provide it as the witness.
3. **`IsPrincipalUnitAbove`**: the image of `ε i` in `((𝓞 K) ⧸ (p))ˣ` is `x ^ Nat.card G = 1` by
   `pow_card_eq_one`. Hence `(ε i : 𝓞 K) - 1 ∈ Ideal.span {(p : 𝓞 K)}`
   (`Ideal.Quotient.eq` / `Ideal.mem_span_singleton`), and `Ideal.span {(p : 𝓞 K)} ⊆ v.asIdeal`
   whenever `(p : 𝓞 K) ∈ v.asIdeal` (`Ideal.span_le`).
4. **`IsMaxRank`**: `logEmbedding K` is an additive monoid hom on `Additive (𝓞 K)ˣ`, so
   `logEmbedding K (Additive.ofMul (u ^ N)) = N • logEmbedding K (Additive.ofMul u)`. Start from
   `NumberField.Units.isMaxRank_fundSystem` and transfer along scaling by the nonzero natural
   `N`: `LinearIndependent.units_smul`, or unfold via `linearIndependent_iff` and cancel `N` (a
   nonzero real scalar).

Off-script bridging tactics likely needed: `Units.ext`, `map_pow`, `nsmul_eq_smul_cast`,
`Nat.cast_ne_zero`.

#### Mathlib lemmas needed (all verified present)
- `NumberField.Units.fundSystem` (`DirichletTheorem.lean:476`)
- `NumberField.Units.isMaxRank_fundSystem` (`Regulator.lean:268`)
- `NumberField.Units.logEmbedding` (`DirichletTheorem.lean`)
- `pow_card_eq_one`, `Ideal.mem_span_singleton`, `Ideal.span_le`, `Ideal.Quotient.eq`
- `LinearIndependent.units_smul` (or `linearIndependent_iff`)

#### Sources
None — this is a satisfiability check demanded by `STATEMENTS.md` ("For each hypothesis, ask
whether any object can satisfy it. An impossible hypothesis makes an implication vacuously
true"), not a claim from the literature.

#### Generality decision
Stated as a bare existential rather than as a `def` producing a distinguished family: no
downstream declaration consumes the witness, so a `def` would be a one-off definition without
API (forbidden by the project's own rule).

#### Stop condition
If this exceeds ~60 lines or hits a mathlib gap, **do not** leave it as `sorry`: the repo has no
`sorry` in any `@[category API]` or `@[category test]` statement. Either split it into its own
PR, or drop the declaration and record the satisfiability argument in the module docstring
instead. Report which was chosen.

---

### [CLEANUP-2] Final `/cleanup` on `LeopoldtConjecture.lean`
- **Status**: open
- **File**: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
- **Depends on**: T004
- **Parallel**: no
- **Type**: cleanup
- **Description**: Final per-file cleanup (cadence rule §1g). Also golf the T004 proof.

---

### [T005] Submission prep
- **Status**: open
- **File**: repo-wide
- **Depends on**: CLEANUP-2
- **Parallel**: no
- **Type**: process
- **Description**:
  1. Open a GitHub issue on `google-deepmind/formal-conjectures` describing the contribution
     (CONTRIBUTING.md step 2); check first for an existing "new conjecture" issue for Leopoldt.
  2. Confirm the Google CLA is signed.
  3. `lake build` clean; `#print axioms` on T004 shows only `propext`, `Quot.sound`,
     `Classical.choice`.
  4. Verify every URL in the module docstring resolves (CONTRIBUTING.md step 7).
  5. Branch off `main` (currently `8323e878`), PR from the `WilliamCoram` fork, link the issue.

---

### [CLEANUP-FINAL] `/cleanup-all` on the touched files
- **Status**: open
- **Depends on**: T005
- **Parallel**: no
- **Type**: cleanup

---

### [T900] (OUT OF SCOPE) `Module ℤ_[p]` on a compact abelian pro-p group
- **Status**: open — deliberately not scheduled
- **File**: would be `FormalConjecturesForMathlib/NumberTheory/…`
- **Depends on**: nothing
- **Type**: infrastructure
- **Description**: Constructing `Module ℤ_[p] (Additive A)` for a compact abelian pro-p group `A`
  (`u ^ a := lim u ^ aₙ`, by extending the ℤ-action along the dense inclusion `ℤ ↪ ℤ_p` and
  proving the module axioms) would let the conjecture be stated in the literal form
  `Module.rank ℤ_[p] ((closure …)) = rank K`. Mathlib has no such instance and no route to one.
  This is a mathlib-sized development and **the current statement does not depend on it**; it is
  recorded so the API gap is not silently forgotten.

# Decomposition for: Leopoldt's conjecture (rank/defect formulation)

This is a **statement-only** project for `google-deepmind/formal-conjectures`, so the
decomposition tree has no proof leaves for the conjecture itself. What is decomposed instead is
the **statement**: each definition it rests on, checked against a verbatim source quote, plus the
two auxiliary declarations that do carry proof obligations.

## Skeleton location

- `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`

`lake build` status: see "Build status" at the end of this file.

## Result R: `Leopoldt.leopoldt_conjecture`

### Plain-English statement

Let `K` be a number field and `p` a prime. Write `r = r₁ + r₂ − 1` for the Dirichlet unit rank of
`K`, `S_p` for the set of primes of `𝓞 K` above `p`, and `U¹_{K_v} = 1 + 𝔪_v ⊆ K_v^×` for the
group of principal (one-)units of the completion at `v ∈ S_p`. The global units embed diagonally,
`ι : 𝓞_K^× → ∏_{v ∈ S_p} K_v^×`; let `E₁ = ι⁻¹(∏_{v ∈ S_p} U¹_{K_v})` be the units that land in the
principal units, and `Ē₁` the topological closure of `ι(E₁)`. **Leopoldt's conjecture** is that
`rank_{ℤ_p} Ē₁ = r`, equivalently that the Leopoldt defect `δ(K,p) = r − rank_{ℤ_p} Ē₁` vanishes,
equivalently that `λ_{K,p} : ℤ_p ⊗_ℤ 𝓞_K^× → ∏_{v ∈ S_p} U¹_{K_v}` is injective.

The Lean rendering fixes a family `ε : Fin r → (𝓞 K)ˣ` of maximal rank lying in `E₁` and asserts
that the only ℤ_p-relation among the `ε i` inside the local principal units is the trivial one —
i.e. that `ker(a ↦ ∏ᵢ (ε i)^{aᵢ}) = 0`, which is `rank_{ℤ_p} Ē₁ = r` (see the equivalence
argument in `plan.md`).

### Leaves

- **L1** (definition, no proof): `Leopoldt.IsPrincipalUnitAbove`

  - Lean statement:
    ```lean
    def IsPrincipalUnitAbove (u : (𝓞 K)ˣ) : Prop :=
      ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → (u : 𝓞 K) - 1 ∈ v.asIdeal
    ```
  - Source: [Nel] = Nelson, arXiv:1308.4637, §1 (p. 1) and §3 (p. 7).
  - Source claim (verbatim, §1 p. 1):
    > "Let π be the uniformizer of p in O_p and define the *principal local units*:
    > O*_{p,1} := 1 + πO_p."

    and (§3, p. 7):
    > "Let Δ be the diagonal embedding of the global units O*_M into the product of local units
    > ∏_{p|p} O*_p and define X := Δ^{-1}(∏_{p|p} O*_{p,1}), i.e., X is the inverse image of the
    > product of the principal local units."
  - Lean ↔ source match: `IsPrincipalUnitAbove K p u` is membership of `u` in `X`. For `u ∈ 𝓞 K`
    and `v ∣ p`, `u ∈ 1 + π𝒪_v` ⟺ `v(u − 1) > 0` ⟺ `u − 1 ∈ v.asIdeal` (the valuation of an
    element of `𝓞 K` is positive exactly when it lies in the prime). The quantifier `∀ v` with
    guard `(p : 𝓞 K) ∈ v.asIdeal` is `∏_{𝔭 ∣ p}`: for a prime ideal `v.asIdeal`, `v ∣ (p)` ⟺
    `p ∈ v.asIdeal`.
  - Corroboration: [Wiki] says the same, "E₁ denotes global units mapping to U₁ (the product of
    local principal units at primes above p)"; [Gras] writes the target as
    `∏_{v ∈ S_p(K)} U¹_{K_v}`.
  - Attacks attempted:
    - [1] *Counterexample / wrong-direction check*: is `u − 1 ∈ v.asIdeal` the right rendering, or
      should it be `u − 1 ∈ v.asIdeal ^ e`? Checked: the source says `1 + π𝒪_p`, i.e. the *first*
      unit group, not a higher one. `π𝒪_p ∩ 𝓞 K = v.asIdeal`. Rendering is right.
    - [2] *Edge cases*: `p = 2` with residue field `𝔽₂` makes the condition vacuous (every unit is
      `≡ 1 mod v`). That is correct, not a bug: for `k_v = 𝔽₂`, `𝒪_v^× = 1 + 𝔪_v` genuinely.
      `p` inert/ramified/split all handled uniformly by the `∀ v` guard. `K = ℚ`: `rank K = 0`, the
      statement degenerates to `a = 0` for `a : Fin 0 → ℤ_[p]`, vacuously true — correct, since
      Leopoldt is trivially true for `ℚ`.
    - [3] *Hypothesis strength*: could the guard be dropped (quantify over all `v`)? No — that
      would force `u ≡ 1` at primes away from `p`, which by finiteness forces `u = 1`; the
      statement would become vacuous. Guard is necessary. Could it be weakened to "some `v ∣ p`"?
      No — [Nel] and [Gras] both take the product over *all* `v ∣ p`; "some" is Nelson's
      *variation*, a different (open) problem.
    - [4] *Source-drift*: re-read [Nel] p. 1 and p. 7. `X` is defined by the *principal* local
      units at *all* primes above `p`. No drift.
    - Verdict: SURVIVED.

- **L2** (definition, no proof): `Leopoldt.IsPadicRelation`

  - Lean statement:
    ```lean
    def IsPadicRelation (ε : Fin (rank K) → (𝓞 K)ˣ) (a : Fin (rank K) → ℤ_[p]) : Prop :=
      ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal →
        Tendsto (fun n : ℕ ↦ ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.adicCompletion K))
          atTop (nhds 1)
    ```
  - Source: [Nel] Lemma 4.2 and its proof (p. 8); [Mih] §1.
  - Source claim (verbatim, [Nel] Lemma 4.2 + proof, p. 8):
    > "Let u₁,…,u_t ∈ O*_M and a₁,…,a_t ∈ Z_p with at least one non-zero. The product
    > u₁^{a₁} ⋯ u_t^{a_t} = 1 in M_p for all p ∈ Γ …"

    > "If u₁^{a₁} ⋯ u_t^{a_t} = 1 in M_p for all p ∈ Γ then there exists a_{j,n} ∈ Z such that
    > p-adically a_{j,n} → a_j and u₁^{a_{1,n}} ⋯ u_t^{a_{t,n}} → 1 in M_p for all p ∈ Γ."

    and ([Mih] §1):
    > "Let Ē = ι(E)‾ = ⋂_{n>0} ι(E)·U^{pⁿ} ⊂ U be the p-adic closure of ι(E)."
  - Lean ↔ source match: the source *defines* the ℤ_p-power `u^{a}` in `M_𝔭` as the limit of
    integer powers `u^{a_n}` along any sequence of integers `a_n → a` p-adically. The Lean
    definition makes that canonical by using mathlib's `PadicInt.appr`, which satisfies
    `x − (x.appr n : ℤ_[p]) ∈ span {p^n}` (`PadicInt.appr_spec`), so `(a i).appr n → a i`
    p-adically. Because each `ε i` is a principal unit at `v` (hypothesis `hone` of R), it lies in
    the pro-p group `1 + 𝔪_v`, so `ε^{pⁿ} → 1` and the limit exists and is independent of the
    choice of approximating sequence. Hence `IsPadicRelation K p ε a` ⟺ `∏ᵢ (ε i)^{aᵢ} = 1` in
    every `K_v`, `v ∣ p`, which is exactly the source's relation.
  - Attacks attempted:
    - [1] *Choice-dependence attack*: does the statement depend on `appr`? For two integer
      approximations `c_n, c'_n` of `a` we have `p^n ∣ c_n − c'_n`, so
      `ε^{c_n}/ε^{c'_n} = (ε^{p^n})^{m}` with `ε^{p^n} → 1` in `1 + 𝔪_v`; the two sequences have
      the same limit. Not choice-dependent. (A `∃ f : Fin r → ℕ → ℤ` variant was considered and is
      equivalent; `appr` was chosen because it is canonical and avoids an existential in the
      hypothesis — see `STATEMENTS.md`' warning about `∃ x, P x → Q`.)
    - [2] *Convergence attack*: does the limit exist at all? Only because `ε i` is principal at
      `v`. Without `hone`, `ε^{c_n}` need not converge (its Teichmüller component `ζ^{c_n}`
      oscillates), so the hypothesis of R would be near-unsatisfiable and R would be vacuous.
      This is exactly why the source introduces `X`, and why `hone` is a hypothesis of R and not
      an afterthought. Guard confirmed necessary.
    - [3] *Edge cases*: `a = 0` gives the constant sequence `∏ ε^0 = 1 → 1`, so
      `IsPadicRelation K p ε 0` holds — the conclusion `a = 0` is therefore attainable and the
      statement is not "always false". `rank K = 0` (i.e. `K = ℚ` or imaginary quadratic): empty
      product, `Tendsto (fun _ ↦ 1) atTop (nhds 1)` holds, conclusion `a = 0` on `Fin 0 → ℤ_[p]`
      is true by `Subsingleton`. Correct.
    - [4] *Direction attack*: is the target `nhds 1` (multiplicative) rather than `nhds 0`? Yes —
      the relation is a product of units equalling `1`. Confirmed against the quoted Lemma 4.2.
    - [5] *Discharge attack (mathlib names)*: `PadicInt.appr` (`RingHoms.lean:356`) and
      `PadicInt.appr_spec` (`RingHoms.lean:405`) verified present with the stated types.
      `HeightOneSpectrum.adicCompletion` verified (`AdicValuation.lean`), and it carries a
      `Valued` topology so `nhds` is meaningful; `CompleteSpace` instance at
      `AdicValuation.lean:726`.
    - Verdict: SURVIVED.

- **L3** (the conjecture, `sorry`): `Leopoldt.leopoldt_conjecture`

  - Lean statement:
    ```lean
    theorem leopoldt_conjecture (ε : Fin (rank K) → (𝓞 K)ˣ) (hmax : IsMaxRank ε)
        (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))
        {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) :
        a = 0
    ```
  - Source claim (verbatim, [Nel] Conjecture 3.1, p. 7):
    > "**Conjecture 3.1 (Leopoldt).** Let M be a number field. Then the Z-rank of O*_M equals the
    > Z_p-rank of Δ(X)‾."

    ([Gras] §1):
    > "λ_{K,p} : ℤ_p ⊗_ℤ 𝒪_K^× ⟶ ∏_{v∈S_p(K)} U¹_{K_v}" … "Leopoldt's conjecture, or Leo(K,p) for
    > short, holds if λ_{K,p} is injective."

    ([Mih] §1):
    > "The difference 𝒟_l(𝕂) = ℤ-rk(E) − ℤ_p-rk(Ē) is called the Leopoldt defect."

    ([Wiki]):
    > "the ℤ_p-module rank of the closure of E₁ embedded diagonally in U₁ equals r₁ + r₂ − 1"

    ([NSW] Theorem 10.3.6, as cited in the secondary literature):
    > "Leopoldt's conjecture for odd p is equivalent to the assertion that the canonical
    > homomorphism Δ : 𝒪_L^× ⊗ ℤ_p → ∏_{𝔓 ∈ S_p(L)} 𝒪̂_𝔓^× is injective."
  - Lean ↔ source match: `IsMaxRank ε` says the `ε i` are ℤ-independent modulo torsion, i.e. they
    generate a finite-index subgroup of `𝓞_K^×` (mathlib:
    `NumberField.Units.isMaxRank_iff_closure_finiteIndex`); together with `hone` they generate a
    finite-index subgroup of Nelson's `X`. The continuous homomorphism
    `φ : ℤ_p^r → ∏_{v ∣ p} U¹_{K_v}`, `a ↦ ∏ᵢ (ε i)^{aᵢ}` has compact source, so its image is the
    closed subgroup `⟨ε⟩‾`, of finite index in `Δ(X)‾` and hence of equal ℤ_p-rank. As `ker φ` is
    a submodule of the free ℤ_p-module `ℤ_p^r` it is free, so
    `rank_{ℤ_p} Δ(X)‾ = r − rank_{ℤ_p}(ker φ)`; therefore
    `rank_{ℤ_p} Δ(X)‾ = r ⟺ ker φ = 0`, which is the Lean conclusion `a = 0`.
    `IsPadicRelation K p ε a` is `φ(a) = 1` by L2. So the Lean theorem is precisely Conjecture 3.1,
    and equally precisely `Leo(K,p)` of [Gras] and `𝒟_l(K) = 0` of [Mih].
  - Attacks attempted:
    - [1] *Weaker-than-Leopoldt attack*: does fixing one family `ε` prove less than injectivity of
      `λ_{K,p}` on all of `ℤ_p ⊗ 𝓞_K^×`? No. `ker λ` is torsion-free (a submodule of
      `ℤ_p ⊗ 𝓞_K^×` modulo the torsion `μ_{p^∞}(K)`, which injects into `U¹_{K_v}` because
      `K ↪ K_v`). If `p^k · ℤ_p^r ⊆ ℤ_p·ε` (finite index), then `p^k · ker λ ⊆ ker φ = 0`, and
      torsion-freeness gives `ker λ = 0`. Equivalent, not weaker.
    - [2] *Stronger-than-Leopoldt attack*: does the ∀-over-`ε` form assert more than Conjecture
      3.1? No — any two max-rank families in `X` are commensurable, so `ker φ = 0` for one iff for
      all. The ∀-form is the same proposition.
    - [3] *Vacuity attack* (`STATEMENTS.md`: "For each hypothesis, ask whether any object can
      satisfy it"): are there `ε` with `IsMaxRank ε` and `IsPrincipalUnitAbove K p (ε i)`? Yes —
      `fundSystem K i ^ N` with `N = Nat.card ((𝓞 K) ⧸ Ideal.span {(p : 𝓞 K)})ˣ`. This is
      discharged by L5 below, which exists precisely to close this attack.
    - [4] *"odd p" attack*: [NSW] 10.3.6 carries an "odd p" hypothesis; the Lean statement has
      none. Checked: [NSW]'s caveat comes from mapping into the *full* local units `𝒪̂_𝔓^×`, where
      at `p = 2` the torsion `{±1}` of `𝒪_K^× ⊗ ℤ_2` interacts badly. The Lean statement maps into
      the *principal* units and quantifies only over a max-rank (hence torsion-free) family, so
      the caveat does not apply — matching [Gras], whose `λ_{K,p}` lands in `U¹_{K_v}` and whose
      statement of `Leo(K,p)` carries no parity hypothesis.
    - [5] *Category attack*: `@[category research open]` — correct as of 2026-09. Mihăilescu
      announced a proof for CM fields (2009–2011, [Mih]) but it is not accepted; the conjecture is
      open in general. Ax–Brumer settles the abelian case, which is recorded separately as L4 with
      `@[category research solved]`.
    - Verdict: SURVIVED.

- **L4** (variant, `sorry`): `Leopoldt.leopoldt_conjecture.variants.abelian`

  - Statement: L3's conclusion under the extra hypothesis `[IsAbelianGalois ℚ K]`.
  - Source (verbatim, [Nel] §1, p. 2):
    > "using a method outlined by J. Ax [1] and A. Brumer's [3] p-adic version of a theorem of
    > A. Baker [2], one can prove that the conjecture is true for abelian extensions of Q, for CM
    > fields with abelian maximal real subfields, and for abelian extensions of imaginary
    > quadratic fields."

    ([Wiki]): "Abelian extensions of ℚ or imaginary quadratic fields (Ax, 1965; Brumer, 1967)".
  - Lean ↔ source match: `IsAbelianGalois ℚ K` is exactly "K is an abelian extension of ℚ".
    Category `research solved`, AMS 11. Mathlib name verified:
    `Mathlib/FieldTheory/Galois/Abelian.lean:25`.
  - Attacks attempted:
    - [1] *Over-claim attack*: Ax–Brumer also covers abelian extensions of imaginary quadratic
      fields; the Lean variant claims only the `ℚ` case, which is a strict sub-claim of what the
      source proves. Safe (under-claiming, not over-claiming). Recorded as a possible future
      addition rather than silently widened.
    - [2] *Attribution attack*: is `research solved` right? Yes — Ax 1965 / Brumer 1967 is
      accepted. No `@[formal_proof]` attribute is added, since no formal proof exists.
    - [3] *Hypothesis attack*: `IsAbelianGalois ℚ K` extends `IsGalois ℚ K`; for a number field
      `Algebra ℚ K` is available, so the class is well-formed. Verified by elaboration.
    - Verdict: SURVIVED.

- **L5** (API lemma, **needs a real proof**): `Leopoldt.exists_isMaxRank_isPrincipalUnitAbove`

  - Statement: `∃ ε, IsMaxRank ε ∧ ∀ i, IsPrincipalUnitAbove K p (ε i)`.
  - Why: `STATEMENTS.md` requires that hypotheses be satisfiable. Without this, L3 could be
    vacuously true.
  - Proof plan: put `N = Nat.card ((𝓞 K) ⧸ Ideal.span {(p : 𝓞 K)})ˣ` (finite, since `𝓞 K` is
    ℤ-free of finite rank so the quotient by `p` has `p^{[K:ℚ]}` elements). Take
    `ε i := fundSystem K i ^ N`.
    - `IsPrincipalUnitAbove`: the image of `ε i` in `((𝓞 K) ⧸ (p))ˣ` is `x^{Nat.card G} = 1`
      (`pow_card_eq_one`), so `ε i − 1 ∈ Ideal.span {(p : 𝓞 K)} ⊆ v.asIdeal` whenever
      `(p : 𝓞 K) ∈ v.asIdeal`.
    - `IsMaxRank`: `logEmbedding K (Additive.ofMul (u ^ N)) = N • logEmbedding K (Additive.ofMul u)`
      (`logEmbedding` is an additive monoid hom), and scaling a linearly independent family by the
      nonzero scalar `N` preserves linear independence. Start from
      `NumberField.Units.isMaxRank_fundSystem`.
  - Mathlib lemmas needed (all verified present): `NumberField.Units.fundSystem`,
    `NumberField.Units.isMaxRank_fundSystem` (`Regulator.lean:268`), `pow_card_eq_one`,
    `Ideal.mem_span_singleton`, `LinearIndependent.units_smul` / `linearIndependent_iff`.
  - Attacks attempted:
    - [1] *`N = 0` attack*: `Nat.card` of a finite nonempty group is `> 0`; the quotient ring is
      finite and its unit group contains `1`, so `N ≥ 1`. Needed for the `IsMaxRank` step (scaling
      by `0` destroys independence). Must be discharged explicitly in the proof.
    - [2] *`rank K = 0` attack*: then `Fin 0 → (𝓞 K)ˣ` and both conjuncts hold vacuously
      (`IsMaxRank` of the empty family is `LinearIndependent` of the empty family, which is true).
      No special-casing needed.
    - [3] *Finiteness attack*: is `(𝓞 K) ⧸ span {(p : 𝓞 K)}` finite? `p ≠ 0` in `𝓞 K` since
      `NumberField K` gives `CharZero`; mathlib has finiteness of `𝓞 K ⧸ I` for nonzero `I`.
      Confirmed as a real (small) proof obligation, not an assumption.
    - Verdict: SURVIVED, with the caveat that this is the one declaration in the file carrying a
      genuine proof obligation. If it turns out to cost more than ~60 lines it should be split
      into its own PR; the conjecture statement does not depend on it.

## API gaps

- **AG1**: `Module ℤ_[p]` on a compact abelian pro-p group (needed only for the *literal*
  `Module.rank ℤ_[p] (Δ(X)‾) = rank K` phrasing).
  - Status: absent from mathlib. Verified: no `Module ℤ_[p]` instance anywhere in
    `Mathlib/`, and no route via `AdicCompletion`, `IsAdicComplete`, or the `ProfiniteGrp`
    category files.
  - Consequence: the chosen statement expresses the same content via limits of integer powers
    (L2), which is how [Nel] Lemma 4.2 and [Mih] both write it. **This project does not depend on
    AG1.**
  - Tracked as `[T900]`, deliberately left open.

## Prior-B2 log

`.mathlib-quality/b2_log.jsonl` does not exist (no prior `/beastmode` run in this repo). No name
or shape matches to check.

## Build status

`lake build FormalConjectures.Wikipedia.LeopoldtConjecture` — **success**, 8895 jobs, only `sorry`
warnings (suppressed for this library by `warn.sorry = false`). No type errors. Repo linters
(`category_docstring`, `ams_attribute`, `latex_docstring`, `moduleDocstring`, `namespace`) all
clean after tagging the API lemma `AMS 11`.

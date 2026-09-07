# Development Plan: Leopoldt's conjecture (rank/defect formulation, no p-adic logarithm)

## Goal

Add a statement-only formalisation of **Leopoldt's conjecture** to
`google-deepmind/formal-conjectures`, in the "defect zero" / rank formulation, i.e. the one
that does **not** require a p-adic logarithm.

Target file: `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`
(sits beside `KummerVandiver.lean`, `ClassNumberProblem.lean`, `RegularPrimes.lean`; there is a
Wikipedia page for the conjecture, which is the repo's usual justification for this directory).
Files are picked up by the `FormalConjectures.+` glob in `lakefile.toml` — no index to update.

## The mathematics

Let `K` be a number field, `p` a prime, `r = r₁ + r₂ - 1 = NumberField.Units.rank K` the Dirichlet
unit rank. Let `S_p` be the primes of `𝓞 K` above `p`, `K_v` the completion at `v ∈ S_p`,
`U¹_{K_v} = 1 + 𝔪_v` the principal (one-)units, and

    λ : 𝓞_K^× ⊗_ℤ ℤ_p ⟶ ∏_{v ∈ S_p} U¹_{K_v}

the map induced by the diagonal embedding. Leopoldt's conjecture says `λ` is injective;
equivalently the ℤ_p-rank of the closure of the image of the global units equals `r`;
equivalently the *Leopoldt defect* `δ(K,p) = r - rank_{ℤ_p}(Ē)` vanishes.

## References (all verified in this session)

| Tag | Source | What it gives us |
| --- | --- | --- |
| [Wiki] | [Wikipedia, *Leopoldt's conjecture*](https://en.wikipedia.org/wiki/Leopoldt%27s_conjecture) | "the ℤ_p-module rank of the closure of E₁ embedded diagonally in U₁ equals r₁ + r₂ − 1", E₁ = global units mapping into U₁, U₁ = product of local **principal** units at primes above p |
| [Nel] | Dawn Nelson, *A Variation on Leopoldt's Conjecture: Some Local Units instead of All Local Units*, [arXiv:1308.4637](https://arxiv.org/abs/1308.4637), §3, Conjecture 3.1 (p. 7) | The precise formulation, with `X := Δ⁻¹(∏_{𝔭∣p} 𝒪*_{𝔭,1})` and the topological closure of `Δ(X)`; also Lemma 4.2 (p. 8), which spells out ℤ_p-powers of units by integer approximation |
| [Mih] | Preda Mihăilescu, *Leopoldt's Conjecture for CM fields*, [arXiv:1105.4544](https://arxiv.org/abs/1105.4544), §1 | `Ē = ι(E)‾ = ⋂_{n>0} ι(E)·U^{pⁿ} ⊂ U`; "The difference 𝒟_l(𝕂) = ℤ-rk(E) − ℤ_p-rk(Ē) is called the Leopoldt defect" |
| [Gras] | Gras et al., *Applications of representation theory and of explicit units to Leopoldt's conjecture*, [arXiv:2301.05700](https://arxiv.org/abs/2301.05700), §1 | `λ_{K,p} : ℤ_p ⊗_ℤ 𝒪_K^× ⟶ ∏_{v ∈ S_p(K)} U¹_{K_v}`; "Leopoldt's conjecture, or Leo(K,p) for short, holds if λ_{K,p} is injective"; `δ(K,p) = dim_{ℚ_p} ker(ℚ_p ⊗ λ_{K,p})`; `Leo(K,p) ⟺ δ(K,p) = 0` |
| [NSW] | Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2008, Theorem 10.3.6 | For odd `p`, Leopoldt ⟺ the canonical map `𝒪_L^× ⊗ ℤ_p → ∏_{𝔓 ∈ S_p(L)} 𝒪̂_𝔓^×` is injective. (Numbering confirmed from secondary literature, not from the book directly — flagged in the file as such.) |
| [Ax] | J. Ax, *On the units of an algebraic number field*, Illinois J. Math. 9 (1965), 584–589 | Leopoldt for abelian extensions of ℚ (with [Bru]) |
| [Bru] | A. Brumer, *On the units of algebraic number fields*, Mathematika 14 (1967), 121–124 | p-adic Baker–Brumer; abelian case |

## Mathlib inventory

| Concept | Mathlib status | Action |
| --- | --- | --- |
| Unit rank `r₁ + r₂ - 1` | `NumberField.Units.rank K` | USE |
| Fundamental system | `NumberField.Units.fundSystem K` | USE |
| "generates a finite-index subgroup" | `NumberField.Units.IsMaxRank` (+ `isMaxRank_iff_closure_finiteIndex`) | USE |
| Primes of `𝓞 K` | `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` | USE |
| Completion `K_v` | `HeightOneSpectrum.adicCompletion K v` (complete valued field, `CompleteSpace`) | USE |
| `𝒪_v` | `HeightOneSpectrum.adicCompletionIntegers K v` (`IsDiscreteValuationRing`) | USE |
| ℤ_p, integer approximation | `ℤ_[p]`, `PadicInt.appr`, `PadicInt.appr_spec` | USE |
| Archimedean regulator | `NumberField.Units.regulator` | not needed |
| **p-adic logarithm** | **absent** | avoided by design |
| **`Module ℤ_[p]` on a pro-p group** | **absent** (no instance anywhere in mathlib) | **API gap — see below** |
| `Subgroup.topologicalClosure` | present | not used in the chosen route |

## Key design decision: why not `Module.rank ℤ_[p] (closure …)` literally

The literal phrasing "the ℤ_p-module rank of the closure of the global units in `U¹`" needs a
`Module ℤ_[p]` structure on `∏_{v ∣ p} U¹_{K_v}`. That structure is real (a compact abelian
pro-p group is canonically a ℤ_p-module, `u ^ a := lim u ^ aₙ`), but **mathlib has no such
instance and no route to one**: there is no `Module ℤ_[p]` instance derived from p-adic
completeness, pro-p-ness, or `AdicCompletion`, and constructing it means extending the
`ℤ`-action along the dense inclusion `ℤ ↪ ℤ_p` and proving the module axioms — a multi-hundred-line
mathlib-sized development, and disproportionate for a statement file.

So the statement expresses the *same* ℤ_p-module content **without** the instance, by writing the
ℤ_p-power `ε ^ a` as the limit of the integer powers `ε ^ (a.appr n)`. This is not an invention:
[Nel] Lemma 4.2 defines ℤ_p-powers of units in `M_𝔭` in exactly this way ("there exists
`a_{j,n} ∈ ℤ` such that p-adically `a_{j,n} → a_j` and `u₁^{a_{1,n}} ⋯ u_t^{a_{t,n}} → 1` in
`M_𝔭`"), and [Mih] writes the closure as `⋂_{n>0} ι(E)·U^{pⁿ}`, which is the same
approximation-by-integer-powers idea.

**Equivalence argument (recorded so a reviewer can check the statement is Leopoldt and not
something weaker).** Fix `ε : Fin r → (𝓞 K)ˣ` of maximal rank whose members are principal units
at every `v ∣ p`. Because each `ε i` lies in the pro-p group `U¹_{K_v}`, the map
`φ : ℤ_p^r → ∏_{v ∣ p} U¹_{K_v}`, `a ↦ ∏ᵢ (ε i)^{aᵢ}` is a well-defined continuous homomorphism
and `φ(a) = lim_n ∏ᵢ (ε i)^{(aᵢ).appr n}`. Its image is `⟨ε⟩‾` (continuous image of a compact
group), which has finite index in `Ē`, hence the same ℤ_p-rank. Since `ker φ` is a ℤ_p-submodule
of the free module `ℤ_p^r`, it is free, so
`rank_{ℤ_p} Ē = r − rank_{ℤ_p}(ker φ)`, and therefore

    rank_{ℤ_p} Ē = r  ⟺  ker φ = 0  ⟺  (∀ a, φ(a) = 1 → a = 0).

That last form is exactly the Lean statement. Passing from a max-rank family to all of
`𝓞_K^× ⊗ ℤ_p` costs nothing: the torsion `μ_{p^∞}(K)` injects into `U¹_{K_v}` because `K ↪ K_v`,
and if `pᵏ·ℤ_p^r ⊆ ℤ_p·ε` then `pᵏ · ker λ ⊆ ker φ = 0` with `ker λ` torsion-free, so `ker λ = 0`.
This is why the statement is uniform in `p` and does not need [NSW]'s "odd p" caveat: restricting
to principal units and to the free part removes the `p = 2` torsion wrinkle.

## File structure

Single file, `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`, containing:

1. `Leopoldt.IsPrincipalUnitAbove` — a unit of `𝓞 K` is `≡ 1` mod every prime above `p`
   (this is membership in [Nel]'s `X`).
2. `Leopoldt.IsPadicRelation` — `∏ᵢ (ε i)^{aᵢ} = 1` in every `K_v`, `v ∣ p`, read as the limit
   of integer powers.
3. `Leopoldt.leopoldt_conjecture` — `@[category research open, AMS 11]`, the conjecture.
4. `Leopoldt.leopoldt_conjecture.variants.abelian` — `@[category research solved, AMS 11]`,
   Ax–Brumer.
5. `Leopoldt.exists_isMaxRank_isPrincipalUnitAbove` — `@[category API]`, non-vacuity of the
   hypotheses (required by `STATEMENTS.md`: "For each hypothesis, ask whether any object can
   satisfy it").

No new `FormalConjecturesForMathlib` file: every definition here is specific to this problem,
which `CONTRIBUTING.md` says belongs in the problem file.

## Generality decisions

- `K` is an arbitrary number field (`[Field K] [NumberField K]`), not restricted to abelian/CM —
  the conjecture is open in general and that is the point of the entry.
- `p` is `(p : ℕ) [Fact p.Prime]`, matching mathlib's `ℤ_[p]` convention. No "odd `p`"
  hypothesis: see the equivalence argument above.
- Primes above `p` are `v : HeightOneSpectrum (𝓞 K)` with `(p : 𝓞 K) ∈ v.asIdeal` rather than an
  `Ideal.LiesOver` instance, so the hypothesis is a plain `Prop` that quantifies uniformly.
- `ε` is quantified universally over *all* max-rank principal families rather than fixed to
  `fundSystem K`; all such families are commensurable so the statements are equivalent, and the
  ∀-form does not force the reader to trust a particular choice.

## Optional follow-on (NOT in scope for this file)

Build `Module ℤ_[p]` on a compact abelian pro-p group in `FormalConjecturesForMathlib/`, then add
the literal `Module.rank ℤ_[p] (closure …) = rank K` phrasing as a second theorem. Substantial
(mathlib-sized); tracked as `[T900]` in the ticket board, deliberately left open.

## ChatGPT validation

`ask_chatgpt_math` was unavailable this session (the `chatgpt-math` MCP server failed to connect),
so step 1h was skipped.

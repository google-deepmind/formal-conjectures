# AEGIS Ω RH exact theorem crosswalk — source vs actual proof obligation

**Snapshot pins:** AEGIS #679 `4d7578ef3df6ae4d1bcd6e2eaefeb2f7f5309afe`; canonical fork #63 parent `9f9bbe7542ecbbfd043d72bff3f4b404075d6da9`. Source archive content is exact, but replay and admission remain head-specific.

| Connected mathematics | Existing exact declaration | What is established / what remains |
|---|---|---|
| Explicit formula | `AEGIS.WeilExplicitFormulaV10.weil_compact_smooth_explicit_formula_v1` | Analytic explicit formula; does not assert global positivity |
| Log-coordinate moment annihilation | `AEGIS.WeilMomentKillerConstructionV1.integral_momentKiller_mul_exp` | Exact moment-cancellation producer |
| Gram expansion | `AEGIS.RHGramExpansionV13.B_packetSum` | Signed cross terms in finite packet sums; global quantifier not discharged |
| Restricted Weil criterion | `AEGIS.WeilRHImpliesFinalSignV13.rh_iff_universal_v13` | RH ↔ universal zero-quadratic sign (equivalence, not proof of either direction unconditionally) |
| Prime-only kernel reduction | fork `AEGIS.RHPrimeOnlyGrowthBridgeV1.riemannHypothesis_of_primeOnly_growth_and_kernel_bridge_v1` | Requires positive-half-line exponential-type-zero **hPrime** and bounded arithmetic/`-K(-t)` comparison **hBridge** |
| Signed-prime V2–V5 work | fork #64 `RHSignedPrimeActualKernelTailV5` | Candidate terminal equivalence, not an unconditional eventual signed-prime bound; replay and arithmetic dictionary needed |
| Local certified positivity | Krein windows / finite M8 certificates | Finite-support theorem ranges; cannot silently extrapolate to all moment-zero test functions |
| Coq concrete finite semantics | `Weil/ConcreteFiniteGuinandWeilSemanticsV1.v`, `Weil/Globalization.v` | Separate Coq proof interfaces; Lean/Coq type correspondence needs a verified bridge |
| Official millennium theorem | `FormalConjectures/Millennium/RiemannHypothesis.lean::RiemannHypothesis.riemannHypothesis` | Exact latest checked replay leaves `AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10` open |

## CI / mathematical separation

An absent `RHRestrictedWeilCriterionV13.olean` means ordinary full-build load order is broken; the direct Lean replay reaches the actual open universal-sign goal, which is a distinct mathematical obligation. Likewise GitHub pre-runner cancellations are **not** Lean proof failures. Never silence the actual unsolved RH goal, add `sorry`, or infer proof from a broad CI green.

**Next falsifiable mathematical step:** search the archived exact source types for an unconditional producer of `FixedKernelArithmeticRemainderBoundedV1` or `SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket)`; compile and axiom-audit that precise producer with its consumer. If none exists, record that missing interface explicitly rather than opening another stacked branch.

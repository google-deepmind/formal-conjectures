# Erdős 768: external proof reproduction

This note records a local reproduction on 24 October 2026 of Eric Li's Lean proof of
[Erdős problem 768](https://www.erdosproblems.com/768). The proof is attributed to
Li and the Aristotle formalization credited in his repository. This is not a claim
of a new mathematical result or of human expert review.

## Source and environment

- [Paper](https://arxiv.org/abs/2606.24872).
- [Proof commit](https://github.com/ericlisg/erdos768-lean/tree/e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9), Apache-2.0.
- Lean `leanprover/lean4:v4.28.0`.
- Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Main declaration: `Erdos768.erdos_768` in `RequestProject/Main.lean`.
- Guarded axiom audit: `RequestProject/AxiomCheck.lean`.

The external proof uses its own pinned environment. It has not been ported to
Formal Conjectures' Lean 4.33.1 environment, and its dependencies are not added to
Formal Conjectures by this note.

## Statement correspondence

`SylowDivisor n` quantifies over every prime divisor `p` of `n` and requires a
divisor `d` of the same `n` with `1 < d` and `d % p = 1`. Since a prime is at least
two, the remainder equation expresses the required congruence.

`Acount x` counts the filtered interval `Finset.Icc 1 ⌊x⌋₊`. Zero is excluded and
one is included. In particular, the counting function is positive for `x ≥ 1`.
The main theorem has no extra hypotheses and proves

\[
\frac{\log(x/A(x))}{\sqrt{\log x}\log\log x}
\longrightarrow \frac{1}{2\sqrt{\log 2}}.
\]

This implies the original exponential form: write
`S(x) = sqrt(log x) * log(log x)` and
`error(x) = log(x/A(x))/S(x) - 1/(2*sqrt(log 2))`.
The limit gives `error(x) → 0`. For `x > exp(1)`, positivity and the exponential/log
identities give exactly
`A(x)/x = exp(-(1/(2*sqrt(log 2)) + error(x))*S(x))`.
Restricting to natural-number inputs gives the original question on `[1,N]`.
This paragraph is a mathematical correspondence argument; the compiled adapter
below states the existential limit formulation.

## Reproduction

With the pinned Lean toolchain installed, use a new checkout:

```sh
git clone https://github.com/ericlisg/erdos768-lean.git erdos768-reproduction
cd erdos768-reproduction
git checkout e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9
lake exe cache get
lake build RequestProject
```

The local run reused a matching Mathlib cache and compiled the external project's
proof modules from source. Its only addition was the following adapter, saved as
`RequestProject/OriginalQuestion.lean` before running `lake build RequestProject`:

```lean
import RequestProject.Main

/-! Adapter from Eric Li's explicit-constant theorem to the existential question.
The imported proof is attributed to https://github.com/ericlisg/erdos768-lean.
-/

open Filter

namespace Erdos768

theorem original_question : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun x : ℝ =>
      Real.log (x / (Acount x : ℝ)) /
        (Real.sqrt (Real.log x) * Real.log (Real.log x))) atTop (nhds c) := by
  refine ⟨c₀, ?_, erdos_768⟩
  unfold c₀
  exact one_div_pos.mpr (mul_pos zero_lt_two (Real.sqrt_pos.mpr (Real.log_pos one_lt_two)))

#print axioms original_question

end Erdos768
```

The build exited successfully after 8,066 jobs, including `RequestProject.Main`,
`RequestProject.OriginalQuestion`, and `RequestProject.AxiomCheck`. The adapter's
axiom output was:

```text
'Erdos768.original_question' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The upstream guarded checks for the main theorem and `MediumPNT` also passed.
There is no `sorryAx` in this dependency closure. These are the standard classical
axioms; the result is not literally axiom-free. The separate upstream
`Challenge.lean` contains an unproved challenge and is not imported by the proved
target. The whole upstream repository should therefore not be described as
containing no placeholders.

## Review scope

Two separate AI agents inspected statement fidelity and selected proof assembly
steps. They did not independently reconstruct every analytic estimate, and this
does not constitute human expert endorsement. Codex performed the local build,
wrote the adapter, and prepared this record at the user's request.

Related submissions are [#4089](https://github.com/google-deepmind/formal-conjectures/pull/4089)
and [#4425](https://github.com/google-deepmind/formal-conjectures/pull/4425).
The latter has a reviewer request to wait for recognition by the Erdős website.
This record supplies reproducibility evidence for that review; it makes no
solved-status metadata change and does not supersede either statement PR.


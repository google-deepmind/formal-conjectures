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
# Erdős Problem 482

*References:*
- [erdosproblems.com/482](https://www.erdosproblems.com/482)
- [GrPo70] Graham, R. L. and Pollak, H. O., Note on a nonlinear recurrence related to {$\surd 2$}. Math. Mag. (1970), 143-145.
- [St05] Stoll, Th., On families of nonlinear recurrences related to digits. J. Integer Seq. (2005), Article 05.3.2, 8.
- [St06] Stoll, Thomas, On a problem of Erd\H{o}s and Graham concerning digits. Acta Arith. (2006), 89-100.
- [RaGi91] Rabinowitz, S. and Gilbert, P., A nonlinear recurrence yielding binary digits. Math. Mag.
  64 (1991), 168-171.

A formal Lean proof is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code.
-/

@[expose] public section

namespace Erdos482

/-- The sequence of the problem: $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$ for
$n \geq 1$. The value $a_0$ is not used. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊√2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊

/-- Stoll's general Graham–Pollak-type recurrence in base $g$, with real parameters $a$, $b$, and
$\varepsilon$. Its even-index differences are used to read base-$g$ digits. -/
noncomputable def generalRecurrence (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((generalRecurrence g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((generalRecurrence g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-- Define a sequence by $a_1=1$ and $$a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor$$ for $n\geq 1$.
The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit in the binary expansion of $\sqrt{2}$.

Find similar results for $\theta=\sqrt{m}$, and other algebraic numbers.

The result for $\sqrt{2}$ was obtained by Graham and Pollak [GrPo70]. The problem statement is
open-ended, but presumably Erdős and Graham would have been satisfied with the wide-ranging
generalisations of Stoll ([St05] and [St06]).

The binary expansion is $\sqrt{2} = 1.0110101\ldots$, and the $n$th digit counts the leading $1$ as
digit $1$.  It is stated with Mathlib's `Real.digits`: the $n$th digit of $\sqrt{2}$ is digit $n - 1$
of $\sqrt{2}/2 = 0.10110101\ldots$, that is $\lfloor \sqrt{2} \cdot 2^{n-1} \rfloor \bmod 2$.  The
second conjunct records that these digits are the binary expansion: they reconstruct $\sqrt{2}/2$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/a28a487968d989b24c9dde9b1958aa5b92c6fccb/LeanGallery/NumberTheory/Erdos482/Statement.lean#L46-L49"]
theorem erdos_482 :
    (∀ n : ℕ, 1 ≤ n →
      (a (2 * n + 1) : ℤ) - 2 * a (2 * n - 1) = (Real.digits (√2 / 2) 2 (n - 1) : ℕ)) ∧
      Real.ofDigits (Real.digits (√2 / 2) 2) = √2 / 2 := by
  sorry

/-- Stoll's general answer to the open-ended part [St05]: for every real $w > 0$ and every base
$g \ge 2$, there are parameters $a$, $b$, and $\varepsilon$, with $ab = g$, such that the
corresponding Graham–Pollak-type recurrence reads the base-$g$ digits of $w$.

The mantissa normalization is $w / g^{\lfloor \log_g w \rfloor}$, so the right-hand side is the
standard Mathlib base-$g$ digit of the normalized expansion. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/a834bbad2f36eedcc16066b2bc4da49f98ab5b85/LeanGallery/NumberTheory/Erdos482/Statement.lean#L64-L67"]
theorem erdos_482.variants.stoll_general (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w) :
    ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ) := by
  sorry

/-- The odd-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)

/-- The even-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)

/-- Zero-based form of the Rabinowitz–Gilbert/Stoll binary recurrence: `stollBinary t k` is the
paper's $u_{k+1}$.  At $t = \sqrt{2}$ both coefficients equal $\sqrt{2}$, and this is the sequence
`a` shifted by one. -/
noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) * ((stollBinary t n : ℝ) + 1 / 2)⌋₊

/-- The binary digits of a normalized real $t \in [1, 2)$, indexed from one and including the
leading digit.  The value at index zero is padding. -/
noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k

/-- The explicit binary answer to the open-ended part [RaGi91], [St05]: for every normalized real
$t \in [1, 2)$, the recurrence with coefficients $\alpha(t) = 2(t+1)/(t+2)$ and
$\beta(t) = (t+2)/(t+1)$ reads off the binary digits of $t$, and those digits reconstruct $t$.
Unlike `erdos_482.variants.stoll_general`, the coefficients are given, not merely shown to exist. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos482.lean#L323-L332"]
theorem erdos_482.variants.binary_explicit (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  sorry

/-- The explicit base-$g$ construction in Stoll [St05, Theorem 1.3]. For a normalized
$t \in [1,g)$, take $a = g/((g-1)(t+g))$ and $b = (g-1)(t+g)$. Every parameter
$-1/g \le \varepsilon < (g+1)(g-2)/g$ gives the same significant digits of $t$.

The sequence is indexed from zero, so the difference at $2n+2$ and $2n$ gives digit $n$,
including the leading digit at $n=0$. The floor difference uses the terminating expansion
when $t$ has two base-$g$ expansions. -/
@[category research solved, AMS 11]
theorem erdos_482.variants.stoll_explicit (g : ℕ) (hg : 2 ≤ g) (t : ℝ)
    (ht : 1 ≤ t) (htg : t < g) (ε : ℝ)
    (hεlo : -1 / (g : ℝ) ≤ ε)
    (hεhi : ε < ((g : ℝ) + 1) * ((g : ℝ) - 2) / g) :
    let a := (g : ℝ) / (((g : ℝ) - 1) * (t + g))
    let b := ((g : ℝ) - 1) * (t + g)
    ∀ n : ℕ,
      generalRecurrence g a b ε (2 * n + 2) -
          (g : ℤ) * generalRecurrence g a b ε (2 * n) =
        ⌊t * (g : ℝ) ^ n⌋ - (g : ℤ) * ⌊t * (g : ℝ) ^ n / g⌋ := by
  sorry

end Erdos482

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
# Erdős Problem 416

*References:*
- [erdosproblems.com/416](https://www.erdosproblems.com/416)
- [OAI26a] OpenAI, *An asymptotic formula for the number of totients*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf
-/

@[expose] public section

open Filter
open scoped Topology Real

namespace Erdos416

/-- Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. -/
noncomputable abbrev V (x : ℝ) : ℝ :=
  open scoped Classical in
  (Finset.Icc 1 ⌊x⌋₊ |>.filter (fun n => ∃ (m : ℕ), m.totient = n)).card

set_option linter.style.formal_proof_palomar false in
/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. Does `V(2x)/V(x)→2` ?

Yes. This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked
Lean proof, which gives `V(cx)/V(x)→c` for every fixed `c>0`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/TotientAsymptotic/UnconditionalMain.lean#L12"]
theorem erdos_416.parts.i :
    Filter.Tendsto (fun x => (V (2 * x) / V (x))) Filter.atTop (𝓝 2) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. Then `V(cx)/V(x)→c` for
every fixed `c>0`, which answers a question of Erdős and Hall. This was proved by an internal
OpenAI model in September 2026 [OAI26a]; see the linked Lean proof.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/TotientAsymptotic/UnconditionalMain.lean#L12"]
theorem erdos_416.variants.regularly_varying (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c) := by
  sorry

/-! ## The main term of [OAI26a]

The definitions in `MainTerm` are those of the Lean statement of [OAI26a, Theorem 2.1], in the
namespace `OAI.TotientAsymptotic` of
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TotientAsymptotic.lean
The docstrings give the notation of [OAI26a, Section 2].
-/

namespace MainTerm

/-- `v` is a value of Euler's totient function at a positive integer. -/
def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

open scoped Classical in
/-- $\ell(v)$, the least $n \ge 1$ with $\varphi(n) = v$. It is `0` if `v` is not a totient. -/
noncomputable def ell (v : ℕ) : ℕ := if h : IsTotient v then Nat.find h else 0

/-- $a_j = (j + 1) \log(j + 1) - j \log j - 1$ [OAI26a, (2.1)]. -/
noncomputable def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

/-- The set of $z \in (0, 1)$ with $\sum_{j \ge 1} a_j z^j = 1$. -/
def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j + 1) * z ^ (j + 1)) = 1}

/-- $\rho$, the root of $\sum_{j \ge 1} a_j \rho^j = 1$ in $(0, 1)$. -/
noncomputable def rho : ℝ := sInf RenewalRootSet

/-- $\lambda = \log(1/\rho)$ [OAI26a, (2.2)]. -/
noncomputable def lam : ℝ := Real.log (1 / rho)

/-- $\gamma = \bigl(\sum_{j \ge 1} j a_j \rho^j\bigr)^{-1}$ [OAI26a, (2.2)]. -/
noncomputable def gamma : ℝ := (∑' j : ℕ, (j + 1 : ℝ) * a (j + 1) * rho ^ (j + 1))⁻¹

/-- $g_0 = 1$ and $g_j = \sum_{d=1}^{j} a_d g_{j-d}$ [OAI26a, (2.2)]. -/
noncomputable def g : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ d ∈ Finset.range (n + 1), a (d + 1) * g (n - d)

/-- $B = \log\log x$ [OAI26a, (2.3)]. -/
noncomputable def B (x : ℝ) : ℝ := Real.log (Real.log x)

/-- $\psi(b) = (\log b - \log\log b) / \lambda$. -/
noncomputable def psi (b : ℝ) : ℝ := (Real.log b - Real.log (Real.log b)) / lam

/-- $m = \lfloor \psi(B) \rfloor$ [OAI26a, (2.3)]. -/
noncomputable def m (x : ℝ) : ℕ := ⌊psi (B x)⌋₊

/-- The phase $\theta = \psi(B) - m$ [OAI26a, (2.3)]. -/
noncomputable def theta (x : ℝ) : ℝ := psi (B x) - m x

/-- $G_j = B^j / (j! \prod_{i=1}^{j} g_i)$ [OAI26a, (2.4)]. -/
noncomputable def G (x : ℝ) (j : ℕ) : ℝ :=
  (B x) ^ j / ((Nat.factorial j : ℝ) * ∏ i ∈ Finset.Icc 1 j, g i)

/-- $P = \lfloor \log\log H \rfloor$. -/
noncomputable def P (H : ℕ) : ℕ := ⌊Real.log (Real.log (H : ℝ))⌋₊

/-- $\alpha_s = \lambda e^{\lambda s}$. -/
noncomputable def alpha (s : ℝ) : ℝ := lam * Real.exp (lam * s)

/-- $P^+(n)$, the largest prime factor of $n$, with $P^+(1) = 1$. -/
def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

/-- The data $\eta = ((Q_h)_{h < H}, a)$ of a tail witness. -/
structure TailDatum (H : ℕ) where
  /-- The numbers $Q_h$. -/
  Q : Fin H → ℕ
  /-- The cofactor $a$. -/
  cofactor : ℕ

/-- $Q_h$ for $h < H$, and `1` otherwise. -/
def tailPrime {H : ℕ} (η : TailDatum H) (h : ℕ) : ℕ :=
  if hH : h < H then η.Q ⟨h, hH⟩ else 1

/-- $v_h = \log\log Q_h$. -/
noncomputable def tailLog {H : ℕ} (η : TailDatum H) (h : ℕ) : ℝ :=
  Real.log (Real.log (tailPrime η h : ℝ))

/-- `η` is a tail witness for the phase `s` [OAI26a, (2.5)]. The entries $Q_h$ with $h < P$ are
not used; they are set to `1`. -/
def IsWitness (H : ℕ) (s : ℝ) (η : TailDatum H) : Prop :=
  (∀ h : Fin H, h.val < P H → η.Q h = 1) ∧
  0 < η.cofactor ∧
  (∀ h ∈ Finset.Ico (P H) H, (tailPrime η h).Prime ∧
    (9 / 10 : ℝ) * alpha s * h * (rho ^ h)⁻¹ ≤ tailLog η h ∧
    tailLog η h ≤ (11 / 10 : ℝ) * alpha s * h * (rho ^ h)⁻¹ ∧
    (∑ l ∈ Finset.Ico (P H) h, a (h - l) * tailLog η l) ≤
      (1 + (1 / 10000 : ℝ) * Real.exp (-(h : ℝ) / 40)) * tailLog η h) ∧
  largestPrimeFactor η.cofactor ≤ tailPrime η (P H) ∧
  Real.log (η.cofactor : ℝ) ≤
    Real.exp (2 * alpha s * (P H : ℝ) * (rho ^ (P H))⁻¹)

/-- $w(\eta) = a \prod_{h=P}^{H-1} Q_h$. -/
noncomputable def w {H : ℕ} (η : TailDatum H) : ℕ :=
  η.cofactor * ∏ h ∈ Finset.Ico (P H) H, tailPrime η h

/-- $W_{H,s}(d)$, the set of tail witnesses $\eta$ with $\varphi(w(\eta)) = d$. -/
def witnesses (H : ℕ) (s : ℝ) (d : ℕ) : Set (TailDatum H) :=
  {η | IsWitness H s η ∧ (w η).totient = d}

/-- $D(h, \eta) = \sum_{l=P}^{H-1} a_{h-l} v_l$ [OAI26a, (2.6)]. -/
noncomputable def D {H : ℕ} (h : ℕ) (η : TailDatum H) : ℝ :=
  ∑ l ∈ Finset.Ico (P H) H, a (h - l) * tailLog η l

open scoped Classical in
/-- $\max_{\eta \in T} D(h, \eta)$. It is `0` if `T` is empty. -/
noncomputable def maxD {H : ℕ} (h : ℕ) (T : Finset (TailDatum H)) : ℝ :=
  if ht : T.Nonempty then T.sup' ht (D h) else 0

open scoped Classical in
/-- The coefficient $A_H(f; s)$ [OAI26a, (2.8)]. -/
noncomputable def AH (H : ℕ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  rho ^ (H * (H - 1) / 2) * (gamma / alpha s) ^ H *
    ∑ᶠ d : ℕ,
      if IsTotient d then
        f ((ell d : ℝ) / d) / d *
          ∑ᶠ T : Finset (TailDatum H),
            if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
              (-1 : ℝ) ^ (T.card - 1) *
                Real.exp (-(gamma / alpha s) *
                  ∑' n : ℕ, rho ^ (H + n) * maxD (H + n) T)
            else 0
      else 0

/-- $A(f; s) = \lim_{H \to \infty} A_H(f; s)$. -/
noncomputable def A (f : ℝ → ℝ) (s : ℝ) : ℝ := limUnder atTop (fun H : ℕ => AH H f s)

/-- The main term $\frac{x}{\log x} G_m A(1; \theta)$ of [OAI26a, Theorem 2.1]. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x / Real.log x * G x (m x) * A (fun _ => 1) (theta x)

end MainTerm

noncomputable def erdos_416.parts.ii.answer : ℝ → ℝ := MainTerm.mainTerm

/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable.
Is there an asymptotic formula for `V(x)`?

Yes. An internal OpenAI model proved in September 2026 that
$V(x) \sim \frac{x}{\log x} G_m A(1; \theta)$ [OAI26a, Theorem 2.1]. Here $x G_m / \log x$ is
Ford's counting scale, and $A(1; \cdot)$ is a function of the phase $\theta \in [0, 1)$ that is
bounded away from $0$ and $\infty$; see `MainTerm.mainTerm`. The
[Lean proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/TotientAsymptotic/UnconditionalMain.lean#L12)
of [OAI26a] proves this with the definitions that are copied in `MainTerm`.
-/
@[category research solved, question value, AMS 11]
theorem erdos_416.parts.ii :
    Filter.Tendsto (fun x => V x / erdos_416.parts.ii.answer x) atTop (𝓝 1) := by
  sorry

/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable.
Pillai proved `V(x)=o(x)`.
Ref: S. Sivasankaranarayana Pillai, _On some functions connected with $\phi(n)$_
-/
@[category research solved, AMS 11]
theorem erdos_416.variants.Pillai : V =o[atTop] id := by
  sorry

/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable.
Erdős proved V(x)=x(logx)^(−1+o(1)).
Ref: Erdős, P., _On the normal number of prime factors of $p-1$ and some related problems concerning Euler's $\varphi$-function._
-/
@[category research solved, AMS 11]
theorem erdos_416.variants.Erdos : ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ᶠ x in Filter.atTop, V x = x * x.log ^ (-1 + f x) := by
  sorry

-- TODO: define the constant from the paper, 0.8178146... here and add it in the statement
def erdos_416.variants.Maier_Pomerance.answer : ℝ := sorry

/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable.
`V(x)=x/logx * e^((C+o(1))(log log log x)^2)`, for some explicit constant `C>0`.
Ref:Maier, Helmut and Pomerance, Carl, _On the number of distinct values of Euler's $\phi$-function_.
-/
@[category research solved, question value, AMS 11]
theorem erdos_416.variants.Maier_Pomerance :
    0 < erdos_416.variants.Maier_Pomerance.answer ∧ ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ᶠ x in Filter.atTop, (V x : ℝ) = x / x.log *
        (rexp <| (erdos_416.variants.Maier_Pomerance.answer + f x) * x.log.log.log ^ 2) := by
  sorry

-- TODO: add the constants `C₁, C₂, C₃` from the paper here
def erdos_416.variants.Ford.answer : ℝ × ℝ × ℝ := sorry

/--
Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable.
`V(x) ≍ x/log x*e^(C_1*(log log log x − log log log log x)^2+C_2 log log log x − C_3 log log log log x)`
Ref: Ford, Kevin, _The distribution of totients_.
-/
@[category research solved, question value, AMS 11]
theorem erdos_416.variants.Ford :
    let (C₁, C₂, C₃) : ℝ × ℝ × ℝ := erdos_416.variants.Ford.answer
    0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    let G (x : ℝ) : ℝ := x / x.log * (rexp <| C₁ * (x.log.log.log - x.log.log.log.log) ^ 2
        + C₂* x.log.log.log - C₃ * x.log.log.log.log)
    V =Θ[atTop] G := by
  sorry

end Erdos416

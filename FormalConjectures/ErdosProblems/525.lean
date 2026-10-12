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
# Erdős Problem 525

*References:*
- [erdosproblems.com/525](https://www.erdosproblems.com/525)
- [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Li66] Littlewood, J. E., _On polynomials $\sum^n \pm z^m$, $\sum^n e^{\alpha_m i} z^m$,
  $z = e^{\theta i}$_. J. London Math. Soc. (1966), 367-376.
- [Ka87] Kashin, B. S., _The properties of random trigonometric polynomials with $\pm 1$
  coefficients_. Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1987), 40-46, 105.
- [Ko94] Konyagin, S. V., _On the minimum modulus of random trigonometric polynomials with
  coefficients $\pm1$_. Mat. Zametki (1994), 80-101, 158.
- [KoSc99] Konyagin, S. V. and Schlag, W., _Lower bounds for the absolute value of random
  polynomials on a neighborhood of the unit circle_. Trans. Amer. Math. Soc. (1999), 4963-4980.
- [CoNg21] Cook, Nicholas A. and Nguyen, Hoi H., _Universality of the minimum modulus for random
  trigonometric polynomials_. Discrete Anal. (2021), Paper No. 20, 46.
-/

@[expose] public section

open Filter Real Finset

namespace Erdos525

/-- The degree-`n` polynomial $f(z)=\sum_{j\leq n}\epsilon_j z^j$ with coefficients
`ε : Fin (n + 1) → ℤˣ`, i.e. $\epsilon_j\in\{-1,1\}$, evaluated at `z`. -/
def eval {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (z : ℂ) : ℂ :=
  ∑ j, ((ε j : ℤ) : ℂ) * z ^ (j : ℕ)

/-- The degree-`n` polynomials with $\pm 1$ coefficients such that $|f(z)|\geq 1$ for all
$|z|=1$. -/
def exceptional (n : ℕ) : Set (Fin (n + 1) → ℤˣ) :=
  {ε | ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖eval ε z‖}

/-- $m(f)=\min_{|z|=1}|f(z)|$. -/
noncomputable def m {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : ℝ :=
  sInf ((fun z ↦ ‖eval ε z‖) '' Metric.sphere (0 : ℂ) 1)

open scoped Classical in
/-- The probability that a uniformly random degree-`n` polynomial with $\pm 1$ coefficients
satisfies `P`. -/
noncomputable def prob (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / 2 ^ (n + 1)

/--
Is it true that all except at most $o(2^n)$ many degree $n$ polynomials with $\pm 1$-valued
coefficients $f(z)$ have $\lvert f(z)\rvert <1$ for some $\lvert z\rvert=1$?

The answer is yes: Littlewood [Li66] conjectured the stronger $m(f)=o(1)$ almost surely, which
was proved by Kashin [Ka87].
-/
@[category research solved, AMS 30 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos525.lean#L118"]
theorem erdos_525.parts.i : answer(True) ↔
    (fun n : ℕ ↦ ((exceptional n).ncard : ℝ)) =o[atTop] fun n : ℕ ↦ (2 : ℝ) ^ n := by
  sorry

/--
What is the behaviour of
$$m(f)=\min_{\lvert z\rvert=1}\lvert f(z)\rvert?$$

Cook and Nguyen [CoNg21] have identified the limiting distribution, proving that for any
$\epsilon>0$
$$\lim_{n\to \infty} \mathbb{P}(m(f) > \epsilon n^{-1/2}) = e^{-\epsilon \lambda}$$
where $\lambda=\sqrt{\pi/12}$.
-/
@[category research solved, AMS 30 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos525.lean#L118"]
theorem erdos_525.parts.ii (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ prob n fun f ↦ ε / √n < m f) atTop
      (nhds (exp (-√(π / 12) * ε))) := by
  sorry

/-- Littlewood [Li66] conjectured that $m(f)=o(1)$ holds almost surely; this was proved by
Kashin [Ka87]. -/
@[category research solved, AMS 30 60]
theorem erdos_525.variants.kashin (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ prob n fun f ↦ m f < δ) atTop (nhds 1) := by
  sorry

/-- Konyagin [Ko94] proved that $m(f)\leq n^{-1/2+o(1)}$ almost surely. -/
@[category research solved, AMS 30 60]
theorem erdos_525.variants.konyagin (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ prob n fun f ↦ m f ≤ (n : ℝ) ^ (-1 / 2 + δ : ℝ)) atTop
      (nhds 1) := by
  sorry

/-- Konyagin and Schlag [KoSc99] proved that for any $\epsilon>0$
$$\limsup_{n\to \infty} \mathbb{P}(m(f) \leq \epsilon n^{-1/2})\ll \epsilon.$$ -/
@[category research solved, AMS 30 60]
theorem erdos_525.variants.konyagin_schlag :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      limsup (fun n : ℕ ↦ prob n fun f ↦ m f ≤ ε / √n) atTop ≤ C * ε := by
  sorry

end Erdos525

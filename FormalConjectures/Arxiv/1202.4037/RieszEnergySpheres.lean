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
# Next-order energy on spheres

Conjecture 3 of [BHS12] asks whether the optimal Riesz energy on $\mathbb S^d$
has a two-term asymptotic expansion for every $d\ge2$. It additionally predicts
an explicit lattice Epstein zeta value for the coefficient when $d=2,4,8,24$.

[BHS12, equation (7)] asks whether the minimum logarithmic energy has an expansion
$W_dN^2-(N/d)\log N+C_{\log,d}N+o(N)$ in arbitrary dimensions. Conjecture 4
predicts the specific value $C_{\log,d}=Z'_{L_d}(0)+d^{-1}\log A_d$ for
$d=2,4,8,24$.

A related problem in [Br11, §3] asks whether the scaled optimal spherical cap
$L^2$ discrepancy has a limit in every dimension $d\ge2$. Stolarsky's invariance
principle connects this limit to the Riesz coefficient at $s=-1$; the specific
lattice values predicted for $d=2,4,8,24$ are discussed in [BB25, §5.3].

*References:*
- [BHS12] J. S. Brauchart, D. P. Hardin and E. B. Saff, *The next-order term for optimal
  Riesz and logarithmic energy asymptotics on the sphere* (2012), Conjectures 3 and 4,
  [arXiv:1202.4037](https://arxiv.org/abs/1202.4037).
- [Br11] J. S. Brauchart, *Optimal discrete Riesz energy and discrepancy*,
  Uniform Distribution Theory 6 (2011), 207–220, §3, Conjectures 3 and 4,
  [arXiv:1103.3088](https://arxiv.org/abs/1103.3088).
- [BB25] D. Bilyk and J. S. Brauchart, *On the lower bounds for the spherical cap
  discrepancy* (2025), §5.3, equations (30) and (33),
  [arXiv:2502.15984](https://arxiv.org/abs/2502.15984).
- [Ki26] Kenta Kitamura, *riesz-energy-spheres*, GitHub repository (2026),
  [repository](https://github.com/KitaKen1/riesz-energy-spheres).
- [dLV16] David de Laat and Frank Vallentin, *A breakthrough in sphere packing:
  the search for magic functions*, Nieuw Archief voor Wiskunde 5/17 (2016),
  184–192, p. 187, [article](https://ir.cwi.nl/pub/24759/24759D.pdf).
-/

@[expose] public section

noncomputable section

namespace RieszSphereFC

open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

/-- The unit sphere $\mathbb S^d\subset\mathbb R^{d+1}$ [BHS12, §1]. -/
abbrev Sphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

/-- Uniform probability measure $\sigma_d$ on $\mathbb S^d$ [BHS12, §1]. -/
def uniform (d : ℕ) : Measure (Sphere d) :=
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))).toSphere
  (μ univ)⁻¹ • μ

/-- The sphere area $A_d=2\pi^{(d+1)/2}/\Gamma((d+1)/2)$ [Ki26]. -/
def area (d : ℕ) : ℝ :=
  2 * Real.pi ^ (((d : ℝ) + 1) / 2) / Real.Gamma (((d : ℝ) + 1) / 2)

/-- The covolume-one triangular theta series [Ki26]. -/
def triangularTheta (t : ℝ) : ℝ :=
  ∑' m : ℤ × ℤ, Real.exp (-2 * Real.pi * t / Real.sqrt 3 *
    ((m.1 : ℝ) ^ 2 + (m.1 : ℝ) * (m.2 : ℝ) + (m.2 : ℝ) ^ 2))

/-- The Leech theta series $(7E_4(it)^3+5E_6(it)^2)/12$ [dLV16, p. 187]. -/
def leechTheta (t : ℝ) : ℝ :=
  let S : ℕ → ℝ := fun k => ∑' n : ℕ,
    (∑ a ∈ Nat.divisors (n + 1), (a : ℝ) ^ k) *
      Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)
  let E₄ := 1 + 240 * S 3
  let E₆ := 1 - 504 * S 5
  (7 * E₄ ^ 3 + 5 * E₆ ^ 2) / 12

/-- Theta series of the covolume-one triangular, $D_4$, $E_8$ and Leech lattices
[BHS12, Conjecture 2; dLV16, p. 187]. Set to $1$ in other dimensions. -/
def latticeTheta (d : ℕ) (t : ℝ) : ℝ :=
  if d = 2 then triangularTheta t
  else if d = 4 then
    ∑' m : Fin 4 → ℤ, if Even (∑ i, m i) then
      Real.exp (-Real.pi * t / Real.sqrt 2 * ∑ i, (m i : ℝ) ^ 2) else 0
  else if d = 8 then
    1 + 240 * ∑' n : ℕ, (∑ a ∈ Nat.divisors (n + 1), (a : ℝ) ^ 3) *
      Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)
  else if d = 24 then leechTheta t
  else 1

/-- The continued Epstein function $Z_L(s)$ in the distance exponent, regular at $s=0$,
using the theta integral for lattices isometric to their duals [Ki26]. -/
def epstein (d : ℕ) (θ : ℝ → ℝ) (s : ℂ) : ℂ :=
  let u := s / 2
  let J : ℂ := ∫ t in Ioi (1 : ℝ), ((θ t - 1 : ℝ) : ℂ) *
    ((t : ℂ) ^ (u - 1) + (t : ℂ) ^ ((d : ℂ) / 2 - u - 1))
  (Real.pi : ℂ) ^ u * ((J - ((d : ℂ) / 2 - u)⁻¹) * (Complex.Gamma u)⁻¹ -
    (Complex.Gamma (u + 1))⁻¹)

/-- The optimal ordered Riesz sum: a minimum for $s\ge0$, a maximum for $s<0$
[BHS12, equation (8)]. -/
def rieszEnergy (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  let E := fun X : Fin N ↪ Sphere d =>
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, dist (X i) (X j) ^ (-s)
  if s < 0 then sSup (range E) else sInf (range E)

/-- The continuous Riesz energy $V_s(\mathbb S^d)$ for $-2<s<d$, extended by its
gamma formula outside that range [BHS12, equation (10)]. -/
def rieszBackground (d : ℕ) (s : ℝ) : ℝ :=
  2 ^ ((d : ℝ) - s - 1) * Real.Gamma (((d : ℝ) + 1) / 2) *
    Real.Gamma (((d : ℝ) - s) / 2) /
      (Real.sqrt Real.pi * Real.Gamma ((d : ℝ) - s / 2))

/-- The minimum ordered logarithmic energy $\mathcal E_{\log}(d,N)$
[BHS12, equation (1)]. -/
def logEnergy (d : ℕ) (N : ℕ) : ℝ :=
  sInf (range fun X : Fin N ↪ Sphere d =>
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j)))

/-- The $L^2$ cap discrepancy, with uniform directions and Lebesgue height measure
on $[-1,1]$ [Br11, Definition 3; Ki26]. -/
def capDiscrepancy (d : ℕ) {N : ℕ} (X : Fin N ↪ Sphere d) : ℝ :=
  let ι : Sphere d → ℝ → Sphere d → ℝ := fun z t x =>
    if t ≤ ⟪(x : EuclideanSpace ℝ (Fin (d + 1))), (z : EuclideanSpace ℝ (Fin (d + 1)))⟫
      then 1 else 0
  Real.sqrt (∫ q, ((∑ i : Fin N, ι q.1 q.2 (X i)) / (N : ℝ) -
    ∫ y, ι q.1 q.2 y ∂(uniform d)) ^ 2
    ∂((uniform d).prod (volume.restrict (Icc (-1 : ℝ) 1))))

/-- The coefficient-existence assertion in [BHS12, Conjecture 3], for every
$d\ge2$ and $-2<s<d+2$, $s\ne0,d$. The trivial case $s=0$ is omitted. -/
@[category research open, AMS 31 52]
theorem riesz_energy {d : ℕ} (hd : 2 ≤ d) {s : ℝ}
    (hs : -2 < s) (hsd : s < (d : ℝ) + 2) (hs0 : s ≠ 0) (hsne : s ≠ (d : ℝ)) :
    ∃ C : ℝ,
      Tendsto (fun N : ℕ =>
        (rieszEnergy d s N - rieszBackground d s * (N : ℝ) ^ 2) /
          (N : ℝ) ^ (1 + s / (d : ℝ)))
        atTop (𝓝 (area d ^ (-s / (d : ℝ)) * C)) := by
  sorry

/-- The lattice-coefficient assertion in [BHS12, Conjecture 3]: for
$d=2,4,8,24$, the Riesz coefficient is $A_d^{-s/d}Z_{L_d}(s)$. -/
@[category research open, AMS 31 52]
theorem riesz_energy_lattice {d : ℕ} (hd : d ∈ ({2, 4, 8, 24} : Finset ℕ)) {s : ℝ}
    (hs : -2 < s) (hsd : s < (d : ℝ) + 2) (hs0 : s ≠ 0) (hsne : s ≠ (d : ℝ)) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy d s N - rieszBackground d s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / (d : ℝ)))
      atTop (𝓝 (area d ^ (-s / (d : ℝ)) *
        (epstein d (latticeTheta d) s).re)) := by
  sorry

/-- Conjecture 3 on $\mathbb S^2$ for $-2<s<2$, $s\ne0$, with the triangular
lattice coefficient [BHS12, Conjecture 3].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem riesz_energy_lattice.variants.dimension_two {s : ℝ}
    (hs : -2 < s) (hsd : s < 2) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 2 s N - rieszBackground 2 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 2))
      atTop (𝓝 (area 2 ^ (-s / 2) * (epstein 2 (latticeTheta 2) s).re)) := by
  sorry

/-- The $D_4$ lattice-coefficient prediction on $\mathbb S^4$ for
$-2<s<4$, $s\ne0$ [BHS12, Conjecture 3]. -/
@[category research open, AMS 31 52]
theorem riesz_energy_lattice.variants.dimension_four {s : ℝ}
    (hs : -2 < s) (hsd : s < 4) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 4 s N - rieszBackground 4 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 4))
      atTop (𝓝 (area 4 ^ (-s / 4) * (epstein 4 (latticeTheta 4) s).re)) := by
  sorry

/-- Conjecture 3 on $\mathbb S^8$ for $-2<s<8$, $s\ne0$, with the $E_8$
coefficient, including its removable value at $s=2$ [BHS12, Conjecture 3].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem riesz_energy_lattice.variants.dimension_eight {s : ℝ}
    (hs : -2 < s) (hsd : s < 8) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 8 s N - rieszBackground 8 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 8))
      atTop (𝓝 (area 8 ^ (-s / 8) * (epstein 8 (latticeTheta 8) s).re)) := by
  sorry

/-- Conjecture 3 on $\mathbb S^{24}$ for $-2<s<24$, $s\ne0$, with the Leech
lattice coefficient [BHS12, Conjecture 3].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem riesz_energy_lattice.variants.dimension_twenty_four {s : ℝ}
    (hs : -2 < s) (hsd : s < 24) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 24 s N - rieszBackground 24 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 24))
      atTop (𝓝 (area 24 ^ (-s / 24) * (epstein 24 (latticeTheta 24) s).re)) := by
  sorry

/-- The coefficient-existence problem in [BHS12, equation (7) and the remark
following Conjecture 4]: for every $d\ge2$, the logarithmic energy has an expansion
$W_dN^2-(N/d)\log N+C_{\log,d}N+o(N)$ for some $C_{\log,d}$. -/
@[category research open, AMS 31 52]
theorem log_energy {d : ℕ} (hd : 2 ≤ d) :
    let W := ∫ p : Sphere d × Sphere d, -Real.log (dist p.1 p.2)
      ∂((uniform d).prod (uniform d))
    ∃ C : ℝ,
      Tendsto (fun N : ℕ =>
        (logEnergy d N - W * (N : ℝ) ^ 2 +
          (N : ℝ) / (d : ℝ) * Real.log N) / (N : ℝ))
        atTop (𝓝 C) := by
  sorry

/-- Conjecture 4 of [BHS12]: in dimensions $2,4,8,24$, the logarithmic energy has
linear coefficient $Z'_{L_d}(0)+d^{-1}\log A_d$, after subtracting
$W_dN^2-(N/d)\log N$. -/
@[category research open, AMS 31 52]
theorem log_energy_lattice {d : ℕ} (hd : d ∈ ({2, 4, 8, 24} : Finset ℕ)) :
    let W := ∫ p : Sphere d × Sphere d, -Real.log (dist p.1 p.2)
      ∂((uniform d).prod (uniform d))
    Tendsto (fun N : ℕ =>
      (logEnergy d N - W * (N : ℝ) ^ 2 +
        (N : ℝ) / (d : ℝ) * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein d (latticeTheta d)) 0).re +
        (1 / (d : ℝ)) * Real.log (area d))) := by
  sorry

/-- Conjecture 4 on $\mathbb S^2$: the linear coefficient is
$Z'_{L_2}(0)+\frac12\log A_2$ [BHS12, Conjecture 4].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem log_energy_lattice.variants.dimension_two :
    let W := ∫ p : Sphere 2 × Sphere 2, -Real.log (dist p.1 p.2)
      ∂((uniform 2).prod (uniform 2))
    Tendsto (fun N : ℕ =>
      (logEnergy 2 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 2 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 2 (latticeTheta 2)) 0).re +
        (1 / 2) * Real.log (area 2))) := by
  sorry

/-- Conjecture 4 on $\mathbb S^4$: the predicted linear coefficient is
$Z'_{D_4}(0)+\frac14\log A_4$ [BHS12, Conjecture 4]. -/
@[category research open, AMS 31 52]
theorem log_energy_lattice.variants.dimension_four :
    let W := ∫ p : Sphere 4 × Sphere 4, -Real.log (dist p.1 p.2)
      ∂((uniform 4).prod (uniform 4))
    Tendsto (fun N : ℕ =>
      (logEnergy 4 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 4 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 4 (latticeTheta 4)) 0).re +
        (1 / 4) * Real.log (area 4))) := by
  sorry

/-- Conjecture 4 on $\mathbb S^8$: the linear coefficient is
$Z'_{E_8}(0)+\frac18\log A_8$ [BHS12, Conjecture 4].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem log_energy_lattice.variants.dimension_eight :
    let W := ∫ p : Sphere 8 × Sphere 8, -Real.log (dist p.1 p.2)
      ∂((uniform 8).prod (uniform 8))
    Tendsto (fun N : ℕ =>
      (logEnergy 8 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 8 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 8 (latticeTheta 8)) 0).re +
        (1 / 8) * Real.log (area 8))) := by
  sorry

/-- Conjecture 4 on $\mathbb S^{24}$: the linear coefficient is
$Z'_{L_{24}}(0)+\frac1{24}\log A_{24}$ [BHS12, Conjecture 4].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem log_energy_lattice.variants.dimension_twenty_four :
    let W := ∫ p : Sphere 24 × Sphere 24, -Real.log (dist p.1 p.2)
      ∂((uniform 24).prod (uniform 24))
    Tendsto (fun N : ℕ =>
      (logEnergy 24 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 24 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 24 (latticeTheta 24)) 0).re +
        (1 / 24) * Real.log (area 24))) := by
  sorry

/-- For every $d\ge2$, the optimal $L^2$ cap discrepancy is asymptotic to
$K_dN^{-1/2-1/(2d)}$ for some $K_d>0$
[Br11, §3, discussion following Proposition 5 and Conjecture 3]. -/
@[category research open, AMS 11 31 52]
theorem cap_discrepancy {d : ℕ} (hd : 2 ≤ d) :
    ∃ K > (0 : ℝ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / (2 * (d : ℝ))) *
        sInf (range fun X : Fin N ↪ Sphere d => capDiscrepancy d X))
        atTop (𝓝 K) := by
  sorry

/-- For $d=2,4,8,24$, the optimal $L^2$ cap discrepancy has coefficient
$\sqrt{-\kappa_d A_d^{1/d}Z_{L_d}(-1)}$
[Br11, Conjecture 4; BB25, §5.3, equations (30), (33)]. -/
@[category research open, AMS 11 31 52]
theorem cap_discrepancy_lattice {d : ℕ} (hd : d ∈ ({2, 4, 8, 24} : Finset ℕ)) :
    let κ := Real.Gamma (((d : ℝ) + 1) / 2) /
      ((d : ℝ) * Real.sqrt Real.pi * Real.Gamma ((d : ℝ) / 2))
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / (2 * (d : ℝ))) *
      sInf (range fun X : Fin N ↪ Sphere d => capDiscrepancy d X))
      atTop (𝓝 (Real.sqrt (-κ * area d ^ (1 / (d : ℝ)) *
        (epstein d (latticeTheta d) (-1)).re))) := by
  sorry

/-- The optimal $L^2$ cap discrepancy on $\mathbb S^2$ has coefficient
$\sqrt{-A_2^{1/2}Z_{L_2}(-1)/4}$ at order $N^{-3/4}$
[Br11, Conjecture 4].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 11 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem cap_discrepancy_lattice.variants.dimension_two :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 4) *
      sInf (range fun X : Fin N ↪ Sphere 2 => capDiscrepancy 2 X))
      atTop (𝓝 (Real.sqrt (-(1 / 4 : ℝ) * area 2 ^ ((1 : ℝ) / 2) *
        (epstein 2 (latticeTheta 2) (-1)).re))) := by
  sorry

/-- The predicted optimal $L^2$ cap discrepancy on $\mathbb S^4$ has coefficient
$\sqrt{-(3/16)A_4^{1/4}Z_{D_4}(-1)}$ at order $N^{-5/8}$
[BB25, §5.3.2]. -/
@[category research open, AMS 11 31 52]
theorem cap_discrepancy_lattice.variants.dimension_four :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) *
      sInf (range fun X : Fin N ↪ Sphere 4 => capDiscrepancy 4 X))
      atTop (𝓝 (Real.sqrt (-(3 / 16 : ℝ) * area 4 ^ ((1 : ℝ) / 4) *
        (epstein 4 (latticeTheta 4) (-1)).re))) := by
  sorry

/-- The optimal $L^2$ cap discrepancy on $\mathbb S^8$ has coefficient
$\sqrt{-(35/256)A_8^{1/8}Z_{E_8}(-1)}$ at order $N^{-9/16}$
[BB25, §5.3.3].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 11 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem cap_discrepancy_lattice.variants.dimension_eight :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 16) *
      sInf (range fun X : Fin N ↪ Sphere 8 => capDiscrepancy 8 X))
      atTop (𝓝 (Real.sqrt (-(35 / 256 : ℝ) * area 8 ^ ((1 : ℝ) / 8) *
        (epstein 8 (latticeTheta 8) (-1)).re))) := by
  sorry

/-- The optimal $L^2$ cap discrepancy on $\mathbb S^{24}$ has coefficient
$\sqrt{-(676039/8388608)A_{24}^{1/24}Z_{L_{24}}(-1)}$ at order $N^{-25/48}$
[BB25, §5.3.3].
The answer is provided by the Lean proof in [Ki26]. -/
@[category research solved, AMS 11 31 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/riesz-energy-spheres/blob/main/lean/FCSolution.lean"]
theorem cap_discrepancy_lattice.variants.dimension_twenty_four :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 48) *
      sInf (range fun X : Fin N ↪ Sphere 24 => capDiscrepancy 24 X))
      atTop (𝓝 (Real.sqrt (-(676039 / 8388608 : ℝ) * area 24 ^ ((1 : ℝ) / 24) *
        (epstein 24 (latticeTheta 24) (-1)).re))) := by
  sorry

end RieszSphereFC

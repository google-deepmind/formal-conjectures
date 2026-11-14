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
# Strong Holevo additivity for qubit channels

Is the Holevo information $\chi$ additive when one factor is a qubit channel? That is, does
$\chi(\Phi \otimes \Omega) = \chi(\Phi) + \chi(\Omega)$ hold for every channel
$\Phi : M_2(\mathbb{C}) \to M_2(\mathbb{C})$ and every channel
$\Omega : M_n(\mathbb{C}) \to M_m(\mathbb{C})$ with $n, m \ge 1$? This is the qubit case of the
additivity problem for the Holevo information. It was known for unital $\Phi$ [King02] and for
$\Phi$ with a pure output [TZBW26], and additivity fails for some channels of high dimension
[Has09]. Here no unitality, rank or symmetry condition is imposed on $\Phi$, and the
optimization for $\Phi \otimes \Omega$ includes entangled inputs. Channels are given by finite
Kraus families.

References:
- [King02] C. King, *Additivity for unital qubit channels*, J. Math. Phys. 43 (2002), 4641.
  https://arxiv.org/abs/quant-ph/0103156
- [Has09] M. B. Hastings, *Superadditivity of communication capacity using entangled inputs*,
  Nature Physics 5 (2009), 255. https://arxiv.org/abs/0809.3972
- [TZBW26] Z. Tang, C. Zhu, G. Bai and X. Wang, *Classical Capacity and Entanglement Cost of
  the Amplitude Damping Channel*, arXiv:2609.28592 (2026). https://arxiv.org/abs/2609.28592
- [Ki26] K. Kitamura, *Strong Holevo additivity for qubit channels*, Lean 4 formalization (2026),
  [GitHub repository](https://github.com/KitaKen1/qubit-strong-additivity/tree/00e82103c022243203f9bfc2da428cc32eea3c78).
-/

@[expose] public section

namespace QubitHolevo

noncomputable section
open scoped ComplexOrder Kronecker
open Matrix

/-- Strong Holevo additivity: $\chi(\Phi \otimes \Omega) = \chi(\Phi) + \chi(\Omega)$ for every
qubit channel $\Phi$ and every channel $\Omega$ between systems of positive finite dimension. -/
@[category research solved, AMS 81 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/qubit-strong-additivity/blob/36cfa17e849e4206fbc6aff30efef414e9c85cb6/lean/QubitAdditivity/FCPresentation.lean#L361"]
theorem strong_additivity {r s n m : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (L : Fin s → Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) (hL : IsKraus L) :
    holevo (tensorKraus K L) = holevo K + holevo L := by
  sorry

/-- Additivity over independent uses: $\chi(\Phi^{\otimes n}) = n\,\chi(\Phi)$ for every qubit
channel $\Phi$. -/
@[category research solved, AMS 81 94,
    formal_proof using lean4 at "https://github.com/KitaKen1/qubit-strong-additivity/blob/36cfa17e849e4206fbc6aff30efef414e9c85cb6/lean/QubitAdditivity/FCPresentation.lean#L369"]
theorem power_additivity {r : ℕ} (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (n : ℕ) : holevo (powerKraus K n) = n * holevo K := by
  sorry

end

end QubitHolevo

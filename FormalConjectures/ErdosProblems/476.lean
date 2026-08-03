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

import FormalConjecturesUtil

/-!
# Erdős Problem 476

*References:*
- [erdosproblems.com/476](https://www.erdosproblems.com/476)
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [dSHa94] Dias da Silva, J. A. and Hamidoune, Y. O., *Cyclic spaces for Grassmann
  derivatives and additive theory*. Bull. London Math. Soc. (1994), 140-146.
-/

namespace Erdos476

/--
Let $A\subseteq \mathbb{F}_p$. Let
$$
A\hat{+}A = \{ a+b : a\neq b \in A\}.
$$
Is it true that
$$
\lvert A\hat{+}A\rvert \geq \min(2\lvert A\rvert-3,p)?
$$

This is the Erdős-Heilbronn inequality, proved by Dias da Silva and Hamidoune.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos476.lean"]
theorem erdos_476 : answer(True) ↔
    ∀ p : ℕ, Fact p.Prime → ∀ A : Finset (ZMod p),
      A.restrictedSumset.card ≥ min (2 * A.card - 3) p := by
  sorry

end Erdos476

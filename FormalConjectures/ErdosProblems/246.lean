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
# Erdős Problem 246

*References:*
- [erdosproblems.com/246](https://www.erdosproblems.com/246)
- [Bi59] Birch, B. J., *Note on a problem of Erd\H{o}s*. Proc. Cambridge
  Philos. Soc. (1959), 370-373.
- [Ca60] Cassels, J. W. S., *On the representation of integers as the sums of
  distinct summands taken from a fixed set*. Acta Sci. Math. (Szeged) (1960),
  111-124.
- [FaCh17] Fang, Jin-Hui and Chen, Yong-Gao, *A quantitative form of the
  {E}rd\H{o}s-{B}irch theorem*. Acta Arith. (2017), 301--311.
- [He00b] Hegyv\'{a}ri, N., *On the completeness of an exponential type
  sequence*. Acta Math. Hungar. (2000), 127--135.
- [Yu24] Yu, Wang-Xing, *On the representation of an exponential type sequence*.
  Publ. Math. Debrecen (2024), 253--261.
-/

namespace Erdos246

/-- The set $\{a^k b^l : k,l \geq 0\}$. -/
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a ^ k * b ^ l}

/--
Let $(a,b)=1$. The set $\{a^kb^l: k,l\geq 0\}$ is complete - that is, every large integer is the sum of distinct integers of the form $a^kb^l$ with $k,l\geq 0$.

We state the nontrivial case $a,b\geq 2$, proved by Birch [Bi59].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos246.lean"]
theorem erdos_246 (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    IsAddComplete (Gamma a b) := by
  sorry

end Erdos246

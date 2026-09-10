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
# Logarithmic-seed pseudorandom generators

Vadhan, *Pseudorandomness*, §7.1.1–§7.1.2, pp. 214–219:
https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.

Definitions 7.3, 7.4 and 7.7 fix stretching, security and uniform computation.
The target is regime (3) on p. 218: seed length $O(\log m)$ and error $1/8$
against circuits of size $m$. Size counts AND/OR gates, with free NOT gates and
inputs, as specified on p. 214. No depth, fan-out, or uniformity restriction
is placed on distinguishers.

The generator and its seed-length function must both be uniformly computable
in time polynomial in the output length. This is equivalent to mild explicitness
in the logarithmic-seed regime. The asymptotic requirements hold for all sufficiently
large output lengths, avoiding impossible stretching at zero and small lengths.
The implication to $\mathrm{BPP}=\mathrm{P}$ is background, not a formal theorem here.
-/

namespace VadhanPseudorandomness

/-- Do uniform polynomial-time $(m,1/8)$ generators with seed length $O(\log m)$
exist for general Boolean circuits? -/
@[category research open, AMS 3 68]
theorem logarithmic_seed_prg : answer(sorry) ↔ ComplexityTheory.LogSeedPRGExists := by
  sorry

end VadhanPseudorandomness

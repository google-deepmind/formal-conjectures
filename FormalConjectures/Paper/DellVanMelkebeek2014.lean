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
# Nondeterministic polynomial advice and complements of NP

Reference: Holger Dell and Dieter van Melkebeek, *Satisfiability Allows No
Nontrivial Sparsification unless the Polynomial-Time Hierarchy Collapses*,
JACM 61(4), Article 23 (2014), abstract, §1, and §2, p.23:8:
https://doi.org/10.1145/2629620.
Author copy: https://pages.cs.wisc.edu/~dieter/Papers/sparsification-jacm.pdf.

The paper uses this noncontainment hypothesis for sparsification and
kernelization lower bounds. Advice is polynomially bounded and depends only
on input length; the underlying verifier belongs to the existing NP class.
-/

namespace DellVanMelkebeek2014

open ComplexityTheory

/-- The class $\mathrm{coNP}$ is not contained in $\mathrm{NP}/\mathrm{poly}$. -/
@[category research open, AMS 68]
theorem coNP_not_subset_NPpoly : ¬ coNP ⊆ NPpoly := by sorry

end DellVanMelkebeek2014

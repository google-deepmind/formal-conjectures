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
# Uniform classes versus polynomial-size circuits

Reference: Ryan Williams, *Algorithms for Circuits and Circuits for Algorithms*
(CCC 2014), §I, §III, Definitions 3.1–3.2, and §III.B:
https://people.csail.mit.edu/rrw/ccc14-survey.pdf.

The classes use actual TM2 computations and nonuniform Boolean DAG families.
The NEXP verifier's time bound is exponential in the original input length.
-/

namespace Williams2014

open ComplexityTheory

/-- Some language in $\mathrm{NP}$ has no polynomial-size Boolean circuit family. -/
@[category research open, AMS 68]
theorem NP_not_subset_Ppoly : ¬ NP ⊆ Ppoly := by sorry

/-- Some language in $\mathrm{EXP}$ has no polynomial-size Boolean circuit family. -/
@[category research open, AMS 68]
theorem EXP_not_subset_Ppoly : ¬ EXP ⊆ Ppoly := by sorry

/-- Some language in $\mathrm{NEXP}$ has no polynomial-size Boolean circuit family. -/
@[category research open, AMS 68]
theorem NEXP_not_subset_Ppoly : ¬ NEXP ⊆ Ppoly := by sorry

end Williams2014

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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture146
import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Regression

/-!
# Axiom audit for Written on the Wall II Conjecture 146

Checks the exact upstream theorem, its raw proof theorem, the exceptional lemma,
and the explicit regression witness.
-/

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WrittenOnTheWallII.GraphConjecture146.Proof.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.conjecture146
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.exceptional_case
#print axioms WrittenOnTheWallII.GraphConjecture146.Proof.Regression.reg_exceptional

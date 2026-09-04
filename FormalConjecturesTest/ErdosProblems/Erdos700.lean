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

import FormalConjectures.ErdosProblems.«700»

/-!
# Regression test for Erdős Problem 700
-/

/--
info: Erdos700.erdos_700.parts.i : {n | ¬Nat.Prime n ∧ 1 < n ∧ Erdos700.f n = n / Erdos700.P n} = sorry
-/
#guard_msgs(info) in
#check Erdos700.erdos_700.parts.i

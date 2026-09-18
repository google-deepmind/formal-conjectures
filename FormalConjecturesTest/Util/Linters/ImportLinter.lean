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

public meta import FormalConjecturesUtil.Linters.ImportLinter

@[expose] public section

open ImportLinter

set_option linter.style.imports true

-- Standard valid import
#guard_msgs in
#check_imports "import FormalConjecturesUtil"

/--
warning: Direct imports from 'Mathlib' (such as 'Mathlib.Data.Nat.Prime.Nth') are disallowed in 'FormalConjectures'. Use 'import FormalConjecturesUtil' instead.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import FormalConjecturesUtil\nimport Mathlib.Data.Nat.Prime.Nth"

/--
warning: Direct imports from 'Mathlib' (such as 'Mathlib') are disallowed in 'FormalConjectures'. Use 'import FormalConjecturesUtil' instead.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import FormalConjecturesUtil\nimport Mathlib"

/--
warning: Direct imports from 'Mathlib' (such as 'Mathlib.Topology.Basic') are disallowed in 'FormalConjectures'. Use 'import FormalConjecturesUtil' instead.

Note: This linter can be disabled with `set_option linter.style.imports false`
---
warning: Files in 'FormalConjectures' must import 'FormalConjecturesUtil'.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import Mathlib.Topology.Basic"

/--
warning: Files in 'FormalConjectures' must import 'FormalConjecturesUtil'.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import FormalConjectures.ErdosProblems.«508»"

/--
warning: Direct imports from 'FormalConjecturesForMathlib' (such as 'FormalConjecturesForMathlib.Combinatorics.Basic') are disallowed in 'FormalConjectures'. Use 'import FormalConjecturesUtil' instead.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import FormalConjecturesUtil\nimport FormalConjecturesForMathlib.Combinatorics.Basic"

/--
warning: Direct imports from 'FormalConjecturesForMathlib' (such as 'FormalConjecturesForMathlib') are disallowed in 'FormalConjectures'. Use 'import FormalConjecturesUtil' instead.

Note: This linter can be disabled with `set_option linter.style.imports false`
-/
#guard_msgs in
#check_imports "import FormalConjecturesUtil\nimport FormalConjecturesForMathlib"

-- When disabled via set_option, no warnings are emitted
set_option linter.style.imports false in
#guard_msgs in
#check_imports "import Mathlib.Topology.Basic"

set_option linter.style.imports false in
#guard_msgs in
#check_imports "import FormalConjecturesForMathlib.Combinatorics.Basic"

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

public import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Printing the group categories using the `↧` notation

Mathlib registers no delaborator for the bundling maps of the group categories, so they print in
full as `AddCommGrpCat.of X`. This file registers `CategoryTheory.delabOf` for them, so that they
print as `↧X`.

This file is copied from [`mathlib4` pull request
#41811](https://github.com/leanprover-community/mathlib4/pull/41811). It can be deleted once that
lands.
-/

public meta section

open Lean.PrettyPrinter.Delaborator

/-- This prints `AddGrpCat.of X` as `↧X`. -/
@[app_delab AddGrpCat.of]
def AddGrpCat.delabOf : Delab := CategoryTheory.delabOf

/-- This prints `GrpCat.of X` as `↧X`. -/
@[app_delab GrpCat.of]
def GrpCat.delabOf : Delab := CategoryTheory.delabOf

/-- This prints `AddCommGrpCat.of X` as `↧X`. -/
@[app_delab AddCommGrpCat.of]
def AddCommGrpCat.delabOf : Delab := CategoryTheory.delabOf

/-- This prints `CommGrpCat.of X` as `↧X`. -/
@[app_delab CommGrpCat.of]
def CommGrpCat.delabOf : Delab := CategoryTheory.delabOf

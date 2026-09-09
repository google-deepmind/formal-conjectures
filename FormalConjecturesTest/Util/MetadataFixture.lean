/-
Copyright 2025 The Formal Conjectures Authors.

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

public import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesUtil.Answer

public section
set_option google.answer "postpone"

namespace MetadataFixture

/-- An assumption retained on an individual proof. -/
theorem assumption : True := by sorry

/-- A quoted declaration with a conditional external proof. -/
@[category research solved, AMS 11,
  conditional formal_proof using lean4 at "https://example.org/conditional"
    assuming assumption]
theorem «quoted name» : True := by trivial

/-- The proposition requested by an open problem. -/
@[category research open, AMS 11]
theorem problem : answer(sorry) ↔ True := by sorry

/-- A variant with a value-valued answer. -/
@[category research solved, AMS 11]
theorem problem.variant : (answer(sorry) : Nat) = 1 := by sorry

@[category test, AMS 11]
example : True := by trivial

end MetadataFixture

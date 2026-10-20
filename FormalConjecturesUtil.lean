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
module -- shake: keep-downstream

public import Mathlib -- shake: keep
public import FormalConjecturesUtil.Linters.AMSLinter -- shake: keep
public import FormalConjecturesUtil.Linters.CategoryDocstringLinter -- shake: keep
public import FormalConjecturesUtil.Linters.CategoryLinter -- shake: keep
public import FormalConjecturesUtil.Linters.CopyrightLinter -- shake: keep
public import FormalConjecturesUtil.Linters.ExistsImplicationLinter -- shake: keep
public import FormalConjecturesUtil.Linters.FormalProofLinter -- shake: keep
public import FormalConjecturesUtil.Linters.ImportLinter -- shake: keep
public import FormalConjecturesUtil.Linters.LatexDocstringLinter -- shake: keep
public import FormalConjecturesUtil.Linters.ModuleDocstringLinter -- shake: keep
public import FormalConjecturesUtil.Linters.NamespaceLinter -- shake: keep
public import FormalConjecturesUtil.Linters.StubLinter -- shake: keep

/-!
# Standard imports for open problems

This file provides Mathlib, the attributes and the linters to every problem file. Problem files
add `public import` lines for the `FormalConjecturesForMathlib` modules they use, so that a change
to one of those modules rebuilds only its importers.

The `shake: keep` annotations tell `scripts/shake_imports.lean` to leave these imports alone.
-/

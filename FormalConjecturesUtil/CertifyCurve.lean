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

public meta import ECCompute.Tactic.CertifyCurve

/-!
# `certify_curve_here`: certified rank lower bounds with file-relative data

`ECCompute` (https://github.com/b-mehta/EllipticCurveRank) provides the tactic `certify_curve`,
which closes a goal `ECCompute.HasRankGE W ρ` for a Weierstrass curve `W` over `ℚ` with integer
coefficients: it reads `ρ` rational points and `ρ` descent labels from two data files, and checks
in the kernel that the points are independent, so that `W(ℚ)` contains a finitely generated
subgroup of rank at least `ρ`.

`certify_curve` resolves its two data-file paths against the working directory of the `lean`
process, which differs between `lake build` at the repository root, the `docbuild/` site build and
an editor session. `certify_curve_here` takes the same arguments but resolves both paths relative
to the directory containing the current source file, so problem files can keep their data next to
them.

This module is deliberately *not* imported by `FormalConjecturesUtil`, so that only the files that
use it depend on `ECCompute`.
-/

public meta section

open Lean Elab Tactic

namespace FormalConjecturesUtil.CertifyCurve

/-- `certify_curve_here torsion p "points.txt" "labels.txt"` is `certify_curve torsion p ...` from
`ECCompute`, with both paths interpreted relative to the directory of the current source file. -/
syntax (name := certifyCurveHere) "certify_curve_here" " torsion " num str str : tactic

/-- Resolve `s` relative to the directory of the file currently being elaborated. -/
def resolveHere (s : StrLit) : TacticM StrLit := do
  let dir : System.FilePath := (System.FilePath.mk (← getFileName)).parent.getD "."
  return Syntax.mkStrLit (dir / s.getString).toString

elab_rules : tactic
  | `(tactic| certify_curve_here torsion $tp:num $path:str $lpath:str) => do
    let path ← resolveHere path
    let lpath ← resolveHere lpath
    evalTactic (← `(tactic| certify_curve torsion $tp $path $lpath))

end FormalConjecturesUtil.CertifyCurve

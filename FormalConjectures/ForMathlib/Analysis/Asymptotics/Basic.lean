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

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open scoped Nat

notation f " ≫ " g => Asymptotics.IsBigO Filter.atTop g f
notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop g f

/-- The type of common functions used to estimate growth rate. -/
inductive ElementaryGrowth : Type
  | const : ℝ → ElementaryGrowth
  | id    : ElementaryGrowth
  | log   : ElementaryGrowth
  | exp   : ElementaryGrowth
  | add   : ElementaryGrowth → ElementaryGrowth → ElementaryGrowth
  | mul   : ElementaryGrowth → ElementaryGrowth → ElementaryGrowth
  | comp  : ElementaryGrowth → ElementaryGrowth → ElementaryGrowth

namespace ElementaryGrowth

/-- The evaluation map of the type of common growth functions. -/
noncomputable def Real.eval : ElementaryGrowth → ℝ → ℝ
  | const c  => fun _ => c
  | id       => fun x => x
  | log      => fun x => x.log
  | exp      => fun x => x.exp
  | add f g  => fun x => eval f x + eval g x
  | mul f g  => fun x => eval f x * eval g x
  | comp f g => eval f ∘ eval g

end ElementaryGrowth

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

import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

/-- A simple graph is planar if it can be embedded in the plane without edge crossings.
According to Kuratowski's theorem, a finite graph is planar if and only if it does not
contain a subdivision of K₅ or K₃,₃.
-/
noncomputable def IsPlanar {α : Type*} (G : SimpleGraph α) : Prop := sorry

end SimpleGraph

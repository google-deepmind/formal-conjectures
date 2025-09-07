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

import FormalConjectures.ForMathlib.Algebra.Group.Indicator
import FormalConjectures.ForMathlib.Algebra.Order.Group.Pointwise.Interval
import FormalConjectures.ForMathlib.Algebra.Polynomial.Basic
import FormalConjectures.ForMathlib.Algebra.Polynomial.HasseDeriv
import FormalConjectures.ForMathlib.AlgebraicGeometry.ProjectiveSpace
import FormalConjectures.ForMathlib.AlgebraicGeometry.VectorBundle
import FormalConjectures.ForMathlib.Analysis.SpecialFunctions.Log.Basic
import FormalConjectures.ForMathlib.Analysis.SpecialFunctions.NthRoot
import FormalConjectures.ForMathlib.Combinatorics.AP.Basic
import FormalConjectures.ForMathlib.Combinatorics.Additive.Basis
import FormalConjectures.ForMathlib.Combinatorics.Additive.Convolution
import FormalConjectures.ForMathlib.Combinatorics.Basic
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.Bipartite
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.Coloring
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.DiamExtra
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants
import FormalConjectures.ForMathlib.Computability.TuringMachine.BusyBeavers
import FormalConjectures.ForMathlib.Computability.TuringMachine.PostTuringMachine
import FormalConjectures.ForMathlib.Data.Nat.Factorization.Basic
import FormalConjectures.ForMathlib.Data.Nat.Full
import FormalConjectures.ForMathlib.Data.Nat.MaxPrimeFac
import FormalConjectures.ForMathlib.Data.Nat.Prime.Defs
import FormalConjectures.ForMathlib.Data.Nat.Prime.Finset
import FormalConjectures.ForMathlib.Data.Nat.Squarefree
import FormalConjectures.ForMathlib.Data.Real.Constants
import FormalConjectures.ForMathlib.Data.Set.Density
import FormalConjectures.ForMathlib.Data.Set.Triplewise
import FormalConjectures.ForMathlib.Geometry.«2d»
import FormalConjectures.ForMathlib.LinearAlgebra.SpecialLinearGroup
import FormalConjectures.ForMathlib.Geometry.«3d»
import FormalConjectures.ForMathlib.Logic.Equiv.Fin
import FormalConjectures.ForMathlib.NumberTheory.AdditivelyComplete
import FormalConjectures.ForMathlib.NumberTheory.CoveringSystem
import FormalConjectures.ForMathlib.NumberTheory.Lacunary
import FormalConjectures.ForMathlib.NumberTheory.WallSunSunPrimes
import FormalConjectures.ForMathlib.Order.Filter.Cofinite
import FormalConjectures.ForMathlib.Order.Interval.Finset.Basic
import FormalConjectures.ForMathlib.Order.Interval.Finset.Nat
import FormalConjectures.ForMathlib.SetTheory.Cardinal.SimpleGraph
import FormalConjectures.ForMathlib.Test.Computability.TuringMachine

import Mathlib.Data.Int.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# The one-step ratio for square-lattice self-avoiding walks

Reference: Bauerschmidt, Duminil-Copin, Goodman and Slade, equation (1.18).
https://arxiv.org/pdf/1206.2092#page=4
-/

namespace SquareLatticeRatio

-- Sample Walk S_n = X_1 +...+ X_n
-- Steps: record of every single step [X_1, ..., X_n]
-- Vertices (steps): record the path [S_0, S_1, ... , S_n]

def displacement : Fin 4 → ℤ × ℤ
  | 0 => (1, 0)    /- Specifies moving directions east, north west south-/
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

  def vertices (steps : List (Fin 4)) : List (ℤ × ℤ) :=
  steps.scanl (fun pos dir =>
    let delta := displacement dir
   (pos.1 + delta.1, pos.2 + delta.2) ) (0, 0) /-here we define the path by vertices-/

#eval decide ((vertices [0, 0]).Nodup)
#eval decide ((vertices [0, 2]).Nodup) /- check whether the path contains a loop -/

#eval vertices [0, 1, 2, 1,2] /-an example of path given some displacements-/

def isSelfAvoiding (steps : List (Fin 4)) : Bool :=
decide ((vertices steps).Nodup) /-check whether steps are self avoiding-/

def allWalks (n : Nat) : List (List (Fin 4)) := -- returns a list of all possible walk of step n
  match n with
  | 0 => [[]]                             -- 0 got to mapped to empty steps
  | k + 1 =>
    let shorter := allWalks k             -- k-step shorter walk
    shorter.flatMap fun walk =>
      (List.finRange 4).map fun d => walk++ [d]

#eval allWalks 0                          -- [[]] check if allwalk function works correctly
#eval (allWalks 2).length                 -- 16
#eval (allWalks 2).countP isSelfAvoiding  -- 12

def walkCount (n : Nat) : Nat :=          -- counting # SelfAvoiding walks C_n
    (allWalks n).countP isSelfAvoiding

#eval walkCount 4                         -- test, should return 100

noncomputable def stepRatio (n : Nat) : ℝ :=          --get C_n
  (walkCount (n + 1) : ℝ) / (walkCount n : ℝ)

#eval (walkCount 4 : Rat) / (walkCount 3 : Rat)  -- test, should return 25/9

noncomputable def rootCount (n : Nat) : ℝ :=         -- Gives C^(1/(n+1))_n
  (walkCount (n + 1) : ℝ) ^ ( 1 / ((n : ℝ) + 1))                --note here we need 1/(n+1) to be real, integer n result 0 on exponential


example : rootCount 0 = 4 := by                                   -- Do some tests to see rootCount behaves qas expected
  norm_num [rootCount, show walkCount 1 = 4 by decide]

example : (rootCount 1) = Real.sqrt 12 := by
  norm_num [rootCount, Real.sqrt_eq_rpow, show walkCount 2 = 12 by decide]

#check rootCount

open scoped Topology

#check fun (u : ℕ → ℝ) (a : ℝ) => Filter.Tendsto u Filter.atTop (𝓝 a) --states limit of a sequence converges

/-Below the main theorem states that there exists a real number μ such that C_{n+1}/C_n and C^{1/(n+1)}_{n+1} converges to
 that real number, where c_n denotes # self-avoiding paths of step n-/
theorem squareLatticeRatio :                                             --the main theorem
    ∃ μ : ℝ,
      Filter.Tendsto rootCount Filter.atTop (𝓝 μ ) ∧                   -- there exists a μ such that root convergence holds
      Filter.Tendsto stepRatio Filter.atTop (𝓝 μ )  := by               -- the mu is also the limit for stepRatio
  sorry



end SquareLatticeRatio

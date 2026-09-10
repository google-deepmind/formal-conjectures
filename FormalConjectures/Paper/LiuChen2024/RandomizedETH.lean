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
import FormalConjecturesUtil

/-!
# Randomized Exponential Time Hypothesis

Reference: Ying Liu and Shiteng Chen, *Sub-Exponential Time Lower Bounds for
#VC and #Matching on 3-Regular Graphs*, STACS 2024, Conjecture 5, p.49:5:
https://doi.org/10.4230/LIPIcs.STACS.2024.49.

The conjecture concerns bounded-error randomized algorithms for 3-SAT.
The operational model is a logarithmic-word RAM, following the fine-grained
conventions of Vassilevska Williams (ICM 2018), §2.1.
The positive exponential rate is written as 1/b, with integer b>0.
-/

namespace LiuChen2024

open FineGrained

/-- Some positive exponential rate cannot be attained by a randomized 3-SAT
algorithm with error at most 1/3, even with a polynomial input-length factor. -/
@[category research open, AMS 68]
theorem randomized_ETH :
    ∃ b : ℕ, 0 < b ∧ ¬ HasSatTime 3 1 b := by sorry

end LiuChen2024

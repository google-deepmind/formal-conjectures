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
# Randomized fine-grained complexity hypotheses

*References:*
* Vassilevska Williams, *On some fine-grained questions in algorithms and
  complexity*, ICM 2018, Hypotheses 1, 2, 4 and 8,
  https://people.csail.mit.edu/virgi/eccentri.pdf.
* Dudek, Gawrychowski and Starikovskaya, *All non-trivial variants of 3-LDT
  are equivalent*, arXiv:2001.01289v1, §1, pp. 2–3,
  https://arxiv.org/pdf/2001.01289v1.
-/

namespace VassilevskaWilliams2018

open FineGrained WordRAM

/-- **Randomized SETH** (Vassilevska Williams, Hypothesis 1), in the time-budget-
width word-RAM model: for every rational $a/b<1$ with $b>0$, some fixed
clause width $k\ge3$ excludes SAT time $C(L+1)^d2^{\lfloor an/b\rfloor}$ for all
fixed $C,d$. The binary formula has length $L$ and $n$ distinct occurring variables;
clauses have at most $k$ literals, retaining empty clauses and repeated occurrences.
One program must halt within the bound on every coin tape and succeed with
probability at least $2/3$ on each input. Word width is
$O(\log(\max(L,T)+2))$, where $T$ is the full time budget, rather than the
survey's input-logarithmic convention; it permits exponential address space. -/
@[category research open, AMS 68]
theorem randomized_SETH :
    ∀ a b : ℕ, 0 < b → a < b → ∃ k : ℕ, 3 ≤ k ∧ ¬ HasSatTime k a b := by sorry

/-- **Integer 3SUM** (Hypothesis 2) has no bounded-error randomized word-RAM
algorithm of time $O(n^{a/b})$ for any $b>0$ and $a/b<2$. Input: a duplicate-free
binary list of $n$ integers in $[-n^4,n^4]$. Property: three distinct entries sum
to zero, following Dudek et al., v1. Inputs with fewer than three entries are no-
instances. Word width is logarithmic in encoded input length; the time bound holds
on every coin tape, with correctness probability at least $2/3$ on every valid
input. This is a fine-grained bound for a problem already in $P$. -/
@[category research open, AMS 68]
theorem integer_threeSum :
    ∀ a b : ℕ, 0 < b → a < 2 * b →
      ¬ HasPowerTimeDecider ValidThreeSum threeSum List.length (fun _ => 1) a b := by sorry

/-- **Orthogonal Vectors** (Hypothesis 4, $k=2$) has no bounded-error randomized
word-RAM algorithm of time $n^{a/b}poly(d)$ for any $b>0$ and $a/b<2$. Input:
two explicitly encoded, duplicate-free sets of $n$ Boolean vectors, each of the
stated dimension $d$. Property: some cross-pair has integer dot product zero,
not merely even parity. All dimensions are included; an empty set yields no pair.
The model has logarithmic-input word width and every-tape time bounds with success
at least $2/3$ on each valid input. This is a fine-grained lower bound within $P$. -/
@[category research open, AMS 68]
theorem orthogonal_vectors :
    ∀ a b : ℕ, 0 < b → a < 2 * b → ¬ HasOVTime a b := by sorry

/-- **Exact Triangle** (Hypothesis 8, $k=3$) has no bounded-error randomized
word-RAM algorithm of time $O(n^{a/b})$ for any $b>0$ and $a/b<3$. Input: a square,
symmetric, loopless matrix of edge-presence flags and binary integer weights in
$[-n^{300},n^{300}]$, including stored unused cells. Property: three distinct
vertices have all three edges present with weight sum exactly zero. Fewer than
three vertices cannot form a triangle. Word width is logarithmic in encoded length;
every coin tape obeys the time bound and each valid input has success at least
$2/3$. This is an exact-sum, not negative-sum, fine-grained problem in $P$. -/
@[category research open, AMS 5 68]
theorem exact_triangle :
    ∀ a b : ℕ, 0 < b → a < 3 * b →
      ¬ HasPowerTimeDecider (ValidWeightedGraph 300) exactTriangle
        List.length (fun _ => 1) a b := by sorry

end VassilevskaWilliams2018

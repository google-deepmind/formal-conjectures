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

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 98

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.98)
- [Bi57] Birch, B. J., *Homogeneous forms of odd degree in a large number of variables*.
  Mathematika 4 (1957), 102--105.
- [Wo98] Wooley, T., *An explicit version of Birch's theorem*. Acta Arith. 85 (1998), 79--96.
- [HB07] Heath-Brown, D. R., *Cubic forms in 14 variables*. Invent. Math. 170 (2007), 199--230.
- [LSZ25] Lampert, A., Snowden, A. and Ziegler, T., *Polynomial bounds for Birch's theorem*.
  [arXiv:2512.00697](https://arxiv.org/abs/2512.00697) (2025).
- [BBGW26] Bonolis, D., Browning, T., Glas, J. and Wang, V. Y., *The Artin-Davenport conjecture on
  cubic forms*. [arXiv:2610.08226](https://arxiv.org/abs/2610.08226) (2026).
-/

@[expose] public section

open Filter Asymptotics

namespace Green98

/--
`HasNontrivialZero d n` says that every homogeneous polynomial $F \in \mathbb{Z}[x_1, \dots, x_n]$
of degree `d` has a zero $x \in \mathbb{Z}^n \setminus \{0\}$. The zero polynomial counts as
homogeneous of every degree; it has nonzero zeros as soon as $n \ge 1$. For $n = 0$ there is no
nonzero $x$, so `HasNontrivialZero d 0` is false.
-/
def HasNontrivialZero (d n : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous d →
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ MvPolynomial.eval x F = 0

/--
`nu d` is $\nu(d)$, the least $\nu$ such that `HasNontrivialZero d n` holds for all $n > \nu$.

For odd `d` the set is nonempty by Birch's theorem (`green_98.variants.birch`), so `nu d` is a
genuine minimum. For even $d \ge 2$ the set is empty (the form $x_1^d + \dots + x_n^d$ has no
nontrivial zero, in any number of variables) and then `sInf ∅ = 0` is a junk value, so we only use
`nu d` for odd `d`.
-/
noncomputable def nu (d : ℕ) : ℕ :=
  sInf {ν : ℕ | ∀ n : ℕ, ν < n → HasNontrivialZero d n}

/--
Wooley's functions $\psi^{(n)}$ [Wo98, (1.5)]: $\psi^{(0)}(x) = \exp(x)$, and for $n > 0$ the value
$\psi^{(n)}(x)$ is obtained from $x$ by applying $\psi^{(n-1)}$ exactly $\lfloor 42 \log x \rfloor$
times, with the natural logarithm.
-/
noncomputable def wooleyPsi : ℕ → ℝ → ℝ
  | 0 => Real.exp
  | n + 1 => fun x ↦ (wooleyPsi n)^[⌊42 * Real.log x⌋₊] x

/--
Wooley's explicit bound $\psi^{((d-5)/2)}(d)$ for one form of odd degree $d \ge 7$
[Wo98, Theorem 1], see `green_98.variants.wooley`.
-/
noncomputable def wooleyBound (d : ℕ) : ℝ :=
  wooleyPsi ((d - 5) / 2) d

/--
Let $d \ge 3$ be an odd integer. Give bounds on $\nu(d)$ such that if $n > \nu(d)$ the following is
true: given any homogeneous polynomial $F(x) = F(x_1, \dots, x_n) \in \mathbb{Z}[x_1, \dots, x_n]$
of degree $d$, there is some $x \in \mathbb{Z}^n \setminus \{0\}$ such that $F(x) = 0$.

Explicit bounds are known: [Gr24] notes that Wooley [Wo98] "gave the first explicit values of
$\nu(d)$, which have tower-type growth in $d$" (`green_98.variants.wooley`). As the open target we
take the possibility that [Gr24] mentions: "So far as I am aware it is considered possible that
$\nu(d) = d^2$, but even the local variant of this (that is, finding solutions in $\mathbb{Q}_p$
rather than $\mathbb{Q}$) is wide open". [Gr24] does not state this as a conjecture, so we record
it as a yes-or-no question: is the least threshold `nu d` equal to $d^2$ for every odd $d \ge 3$?

For $d = 3$ the equality $\nu(3) = 9$ follows from the 2026 preprint [BBGW26]
(`green_98.variants.cubic_ten`) and the lower bound recalled in [LSZ25] ("it is known that at
least 10 variables are required"). The question is open for $d \ge 5$.
-/
@[category research open, question, AMS 11]
theorem green_98 : ∀ d : ℕ, Odd d → 3 ≤ d → nu d = d ^ 2 := by
  sorry

def green_98.variants.order.answer : ℕ → ℝ := sorry

/--
The order of growth of the least threshold $\nu(d)$ (`nu`) along the odd degrees $d = 2k + 3$, up
to constant factors. If the answer to `green_98` is yes, this is $k^2$.
-/
@[category research open, question value, AMS 11]
theorem green_98.variants.order :
    (fun k : ℕ ↦ (nu (2 * k + 3) : ℝ)) =Θ[atTop] green_98.variants.order.answer := by
  sorry

/--
**Birch's theorem.** For every odd $d$ the number $\nu(d)$ exists: there is $\nu$ such that every
homogeneous integral form of degree $d$ in more than $\nu$ variables has a nontrivial integer
zero [Bi57]. (We checked the formulation against the statement of Birch's theorem for number
fields recalled in the introduction of [LSZ25], here for one form over $K = \mathbb{Q}$.) [Gr24]
notes that the first explicit values of $\nu(d)$, of tower type, are due to Wooley [Wo98], see
`green_98.variants.wooley`.
-/
@[category research solved, AMS 11]
theorem green_98.variants.birch :
    ∀ d : ℕ, Odd d → ∃ ν : ℕ, ∀ n : ℕ, ν < n → HasNontrivialZero d n := by
  sorry

/--
**Wooley's explicit version of Birch's theorem** [Wo98, Theorem 1], for one form and a nontrivial
zero ($r = 1$, $m = 0$ there): "Let $d$ be an odd integer exceeding $5$ [...] Then
$v^{(m)}_{d,r}(\mathbb{Q}) < \psi^{((d-5)/2)}(dr(m+1))$." Here $v_{d,1}(\mathbb{Q})$ is the least
integer such that every rational form of degree $d$ in more than that many variables has a
nontrivial rational zero, which is $\nu(d)$ after clearing denominators. So every integral form of
odd degree $d \ge 7$ in $n \ge \psi^{((d-5)/2)}(d)$ variables has a nontrivial integer zero.
-/
@[category research solved, AMS 11]
theorem green_98.variants.wooley :
    ∀ d : ℕ, Odd d → 7 ≤ d → ∀ n : ℕ, wooleyBound d ≤ (n : ℝ) → HasNontrivialZero d n := by
  sorry

/--
**Heath-Brown's theorem on cubic forms** [HB07]: a cubic form over $\mathbb{Q}$ in at least $14$
variables has a nontrivial zero, with no nonsingularity assumption ([LSZ25] recall that "14
variables are sufficient"). Clearing denominators, this is the statement that every integral cubic
form in $n \ge 14$ variables has a nontrivial integer zero, that is, $\nu(3) \le 13$ as in [Gr24].
It is improved by `green_98.variants.cubic_ten`.
-/
@[category research solved, AMS 11]
theorem green_98.variants.heath_brown : ∀ n : ℕ, 14 ≤ n → HasNontrivialZero 3 n := by
  sorry

/--
**Bonolis--Browning--Glas--Wang** [BBGW26] (a 2026 preprint): "any integral cubic form in ten or
more variables has a nontrivial integer zero", that is, $\nu(3) \le 9$. Together with the lower
bound $\nu(3) \ge 9$ recalled in [LSZ25] ("it is known that at least 10 variables are required"),
this gives $\nu(3) = 9$, the case $d = 3$ of `green_98`.
-/
@[category research solved, AMS 11]
theorem green_98.variants.cubic_ten : ∀ n : ℕ, 10 ≤ n → HasNontrivialZero 3 n := by
  sorry

end Green98

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
# Poisson $n$-Lie algebra construction from scalar matrices and commuting derivations

*References:*
- [arxiv/2605.01785](https://arxiv.org/abs/2605.01785)
  **Poisson $n$-Lie algebras: constructions and the structure of solvable algebras**
  by *Xinru Cao, Zafar Normatov, Bakhrom Omirov* (2026)
- In particular, **Conjecture 3.5** (page 9) and **Proposition 3.4** of that paper.

## Setup

Let $(\mathcal{A}, \cdot)$ be a unital commutative associative algebra over a field $\mathbb{F}$
equipped with $n+m$ pairwise commuting derivations $d_1, \dots, d_{n+m}$, where $n \ge 2$ and
$m \ge 1$. Let $A \in M_{(n+m) \times m}(\mathbb{F})$ be a fixed matrix with **scalar** entries
$a_{r,s} \in \mathbb{F}$ (not in $\mathcal{A}$). The $n$-ary determinant bracket is defined by:

$$[x_1, \dots, x_n] = \det \begin{pmatrix}
d_1(x_1) & \cdots & d_1(x_n) & a_{1,1} & \cdots & a_{1,m} \\
\vdots    & \ddots & \vdots    & \vdots   & \ddots & \vdots   \\
d_{n+m}(x_1) & \cdots & d_{n+m}(x_n) & a_{n+m,1} & \cdots & a_{n+m,m}
\end{pmatrix}$$

The **Filippov fundamental identity** (higher Jacobi identity, making this an $n$-Lie algebra)
for fixed index $k$ and tuples $x, y : \mathrm{Fin}\, n \to \mathcal{A}$:
$$[x_1, \dots, x_{k-1}, [y_1, \dots, y_n], x_{k+1}, \dots, x_n] =
  \sum_{i=1}^n [y_1, \dots, y_{i-1}, [x_1, \dots, x_{k-1}, y_i, x_{k+1}, \dots, x_n],
    y_{i+1}, \dots, y_n]$$

The **Leibniz rule** (making the bracket a derivation of the commutative product) for index $k$:
$$[x_1, \dots, x_{k-1}, a \cdot b, x_{k+1}, \dots, x_n] =
  [x_1, \dots, x_{k-1}, a, x_{k+1}, \dots, x_n] \cdot b
  + a \cdot [x_1, \dots, x_{k-1}, b, x_{k+1}, \dots, x_n]$$

When both hold, $(\mathcal{A}, \cdot, [-,\dots,-])$ is called a **Poisson $n$-Lie algebra**.
-/

namespace Arxiv.«2605.01785»

variable {F : Type*} [Field F]
variable {A : Type*} [CommRing A] [Algebra F A]
variable {n m : ℕ}

/- ## The $n$-ary determinant bracket -/

/-- The $(n+m) \times (n+m)$ matrix whose first $n$ columns are $[d_{i}(x_j)]_{i,j}$ and
whose last $m$ columns carry the scalar matrix $M$ embedded into $A$ via `algebraMap`. -/
noncomputable def bracketMatrix
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) : Matrix (Fin (n + m)) (Fin (n + m)) A :=
  Matrix.of fun i j =>
    if h : j.val < n
    then d i (x ⟨j.val, h⟩)
    else algebraMap F A (M i ⟨j.val - n, by omega⟩)

/-- The $n$-ary determinant bracket $[x_1, \dots, x_n]$ arising from $n + m$ pairwise commuting
derivations $d_1, \dots, d_{n+m}$ and a scalar matrix $M \in M_{(n+m) \times m}(\mathbb{F})$.

The value is the determinant of the $(n + m) \times (n + m)$ matrix whose first $n$ columns are
$[d_r(x_j)]$ and whose last $m$ columns are the algebra-map image of $M$. -/
noncomputable def nLieBracket
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) : A :=
  Matrix.det (bracketMatrix d M x)

/- ## Poisson $n$-Lie algebra axioms -/

/-- The **Filippov fundamental identity** for an $n$-ary map `b : (Fin n → A) → A`.

For any index `k : Fin n` and any two tuples `x y : Fin n → A`, the bracket acts as an inner
derivation (in the $n$-Lie sense) in the `k`-th slot:
$$b(x[k \leftarrow b(y)]) = \sum_{i} b(y[i \leftarrow b(x[k \leftarrow y\,i])])$$
This generalises the Jacobi identity to the $n$-ary setting. -/
def FilippovIdentity (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (y : Fin n → A) (k : Fin n),
    b (Function.update x k (b y)) =
      ∑ i : Fin n,
        b (Function.update y i (b (Function.update x k (y i))))

/-- The **Leibniz rule** for an $n$-ary map `b`: the bracket is a derivation of the algebra
product in any chosen slot `k : Fin n`:
$$b(x[k \leftarrow a \cdot c]) = b(x[k \leftarrow a]) \cdot c + a \cdot b(x[k \leftarrow c])$$ -/
def LeibnizRule (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (k : Fin n) (a c : A),
    b (Function.update x k (a * c)) =
      b (Function.update x k a) * c + a * b (Function.update x k c)

/-- The bracket is **alternating**: swapping any two arguments negates the value. -/
def Alternating (b : (Fin n → A) → A) : Prop :=
  ∀ (x : Fin n → A) (i j : Fin n), i ≠ j →
    b (x ∘ Equiv.swap i j) = -(b x)

/-- A **Poisson $n$-Lie algebra** structure on `A`: the bracket is alternating, satisfies
the Filippov fundamental identity, and satisfies the Leibniz rule. -/
def IsPoissonNLie (b : (Fin n → A) → A) : Prop :=
  Alternating b ∧ FilippovIdentity b ∧ LeibnizRule b

/- ## Results from the paper (proved cases) -/

/--
**Proposition 3.4 (Cao–Normatov–Omirov, 2026).** For $n = 3$ and $m = 2$, the $3$-ary
determinant bracket arising from any 5 pairwise commuting derivations and any scalar matrix
$M \in M_{5,2}(\mathbb{F})$ makes $(\mathcal{A}, \cdot, [-,-,-])$ a Poisson 3-Lie algebra.

The proof in the paper uses a case analysis on $|I \cap J| = 3, 2, 1$ combined with the
Grassmann–Plücker relations.
-/
@[category research solved, AMS 17]
theorem poissonThreeLie_of_scalarMatrix
    (d : Fin (3 + 2) → Derivation F A A)
    (hcomm : ∀ i j : Fin (3 + 2), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (3 + 2)) (Fin 2) F) :
    IsPoissonNLie (n := 3) (nLieBracket d M) := by
  sorry

/--
**Solved for $n = 4$, $m = 2$ (Cao–Normatov–Omirov, 2026).** The $4$-ary determinant bracket
arising from any 6 pairwise commuting derivations and a scalar matrix $M \in M_{6,2}(\mathbb{F})$
makes $(\mathcal{A}, \cdot, [-,-,-,-])$ a Poisson 4-Lie algebra.

Stated after Proposition 3.4 in the paper: "By arguments analogous to those used in the proof
of Proposition 3.4, one can show that $(\mathcal{A}, [-,-,-,-])$ forms a Poisson 4-Lie algebra
for any scalar matrix $A \in M_{6,2}(\mathbb{F})$."
-/
@[category research solved, AMS 17]
theorem poissonFourLie_of_scalarMatrix_m2
    (d : Fin (4 + 2) → Derivation F A A)
    (hcomm : ∀ i j : Fin (4 + 2), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (4 + 2)) (Fin 2) F) :
    IsPoissonNLie (n := 4) (nLieBracket d M) := by
  sorry

/--
**Solved for $n = 4$, $m = 3$ (Cao–Normatov–Omirov, 2026).** The Poisson 4-Lie structure
also holds for scalar matrices $M \in M_{7,3}(\mathbb{F})$.

Stated after Proposition 3.4 in the paper.
-/
@[category research solved, AMS 17]
theorem poissonFourLie_of_scalarMatrix_m3
    (d : Fin (4 + 3) → Derivation F A A)
    (hcomm : ∀ i j : Fin (4 + 3), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (4 + 3)) (Fin 3) F) :
    IsPoissonNLie (n := 4) (nLieBracket d M) := by
  sorry

/- ## The main open conjecture -/

/--
**Conjecture 3.5 (Cao–Normatov–Omirov, 2026).** For all integers $n \ge 2$ and $m \ge 1$,
the $n$-ary determinant bracket defined by any $n + m$ pairwise commuting derivations of a
unital commutative associative $\mathbb{F}$-algebra and any scalar matrix
$A \in M_{(n+m) \times m}(\mathbb{F})$ makes the algebra a **Poisson $n$-Lie algebra**.

- **Proved:** $n = 3$ (Proposition 3.4) and $n = 4$ (remark after Prop. 3.4).
- **Open:** All $n \ge 5$, and the general case for arbitrary $n \ge 2$.

*Source:* [Conjecture 3.5, page 9 of arXiv:2605.01785](https://arxiv.org/pdf/2605.01785#page=9)
-/
@[category research open, AMS 17]
theorem poissonNLie_of_scalarMatrix (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Algebra F A]
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    IsPoissonNLie (nLieBracket d M) := by
  sorry

/- ## Tests -/

/--
The bracket vanishes whenever two arguments coincide: $[x_1, \dots, x_n] = 0$ when $x_i = x_j$
for some $i \ne j$. This follows from the fact that two columns of `bracketMatrix` become equal,
so its determinant is zero.
-/
@[category test, AMS 17]
theorem nLieBracket_eq_zero_of_repeat
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) (heq : x i = x j) :
    nLieBracket d M x = 0 := by
  simp only [nLieBracket, bracketMatrix]
  -- Embed `i j : Fin n` as column indices in `Fin (n + m)` then apply the det lemma
  apply Matrix.det_zero_of_column_eq
    (i := ⟨i.val, i.isLt.trans_le (Nat.le_add_right n m)⟩)
    (j := ⟨j.val, j.isLt.trans_le (Nat.le_add_right n m)⟩)
  · exact fun h => hij (Fin.ext (Fin.mk.inj h))
  · intro r
    simp only [Matrix.of_apply, i.isLt, j.isLt, dif_pos, heq]

/--
The Leibniz rule for `nLieBracket` holds: the bracket is additive in each argument slot `k`.
This is the additivity part of the Leibniz rule, which follows from multilinearity of the
determinant.
-/
@[category test, AMS 17]
theorem nLieBracket_add_in_slot
    (d : Fin (n + m) → Derivation F A A)
    (M : Matrix (Fin (n + m)) (Fin m) F)
    (x : Fin n → A) (k : Fin n) (a b : A) :
    nLieBracket d M (Function.update x k (a + b)) =
      nLieBracket d M (Function.update x k a) +
      nLieBracket d M (Function.update x k b) := by
  simp only [nLieBracket]
  -- Follows from multilinearity of the determinant and additivity of derivations
  sorry

end Arxiv.«2605.01785»

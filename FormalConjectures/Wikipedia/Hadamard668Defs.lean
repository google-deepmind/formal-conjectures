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
# The order-668 Hadamard matrix construction

This file defines a Hadamard matrix of order 668 from the cyclic sign sequences in the example
announced by Levent Alpöge, Philippe Voinov, Saul Reynolds-Haertle, and Claude. Rotating a
sequence, reading it backwards, or changing every sign preserves the identity used below. The
stored sequences are representatives obtained this way from the announced example, arranged in
a different block pattern from the posted matrix.

## Construction

Let $a,b,c,d : \mathbb Z/166\mathbb Z \to \{\pm1\}$ be the four sign sequences stored in
`sBits`. For a sequence $x$, define $S(x)_{ij}=x_{i-j}$, and let $R$ be the permutation matrix
for $i\mapsto-i$. Write $A=S(a),\ldots,D=S(d)$. These matrices form the $664\times664$ core

$$
M=\begin{pmatrix}
A&BR&CR&DR\\
-BR&A&D^\mathsf{T}R&-C^\mathsf{T}R\\
-CR&-D^\mathsf{T}R&A&B^\mathsf{T}R\\
-DR&C^\mathsf{T}R&-B^\mathsf{T}R&A
\end{pmatrix}.
$$

Let $X,Y,Z$ be the fixed $4\times4$ matrices defined below. Repeating each entry of $Y$ and $Z$
across 166 positions gives matrices $\widetilde Y$ of size $4\times664$ and $\widetilde Z$ of size
$664\times4$. The final matrix is

$$
H=\begin{pmatrix}X&\widetilde Y\\\widetilde Z&M\end{pmatrix},
\qquad \dim H=4+4\cdot166=668.
$$

## Why it works

With indices taken modulo 166, the four sequences satisfy

$$
P(t)=\sum_i(a_i a_{i+t}+b_i b_{i+t}+c_i c_{i+t}+d_i d_{i+t})
=\begin{cases}664,&t=0,\\-4,&t\ne0.\end{cases}
$$

Writing $J_{166}$ for the all-ones matrix, the diagonal $166\times166$ blocks of
$M^\mathsf{T}M$ are $668I_{166}-4J_{166}$, while its other blocks vanish. The border supplies the
missing $4J_{166}$ in each diagonal block and cancels the cross terms. Hence
$H^\mathsf{T}H=668I_{668}$; since every entry of $H$ is $\pm1$, it is a Hadamard matrix.

*References:*
- [Order-668 construction](https://x.com/__alpoge__/status/2087504785952182273)
  by *Levent Alpöge et al.* (2026)
- [Construction credits](https://x.com/__alpoge__/status/2087504790435840207)
-/

open Matrix

namespace Hadamard

abbrev C := Fin 166
abbrev Q := Fin 4

-- The matrix construction

/-- Packed forms of the four length-166 sign sequences; a set bit means $+1$. -/
def sBits : Q → BitVec 166 :=
  ![0x125953fe2c4fbd9e46d5424b2a5fc58e084c372557#166,
    0x383e32a915b5fb694a447f07c65522b4c092deb770#166,
    0x71876112ff7760ef2e578e30ec225fd913e21a350#166,
    0x14c464e997f8fcd16f35c2988c8d32fce065d21947#166]

/-- Decode one entry of a stored sequence as the integer $+1$ or $-1$. -/
def s (q : Q) (i : C) : ℤ := if (sBits q).getLsb i then 1 else -1

/-- The permutation matrix $R$ for the map $i \mapsto -i$ on $\mathbb Z/166\mathbb Z$. -/
def R : Matrix C C ℤ := (Equiv.neg C).permMatrix ℤ

/-- The circulant matrix $S(x)$ with entries $S(x)_{ij}=x_{i-j}$. -/
def S (x : C → ℤ) : Matrix C C ℤ := Matrix.circulant x

/-- The $4\times4$ block array defining the $664\times664$ core matrix. -/
def M_blocks (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := S a
  let B := S b
  let C := S c
  let D := S d
  !![A, B * R, C * R, D * R;
     -(B * R), A, D.transpose * R, -(C.transpose * R);
     -(C * R), -(D.transpose * R), A, B.transpose * R;
     -(D * R), C.transpose * R, -(B.transpose * R), A]

/-- The $664\times664$ core matrix $M$. -/
def M : Matrix (Q × C) (Q × C) ℤ := fun i j =>
  M_blocks (s 0) (s 1) (s 2) (s 3) i.1 j.1 i.2 j.2

/-- The fixed $4\times4$ northwest block $X$. -/
def X : Matrix Q Q ℤ :=
  !![-1, 1, 1, -1;
      1, -1, 1, -1;
      1, 1, -1, -1;
      -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Y$ for the top-right block. -/
def Y : Matrix Q Q ℤ :=
  !![1, -1, -1, 1;
     1, -1, 1, -1;
     1, 1, -1, -1;
     -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Z$ for the bottom-left block. -/
def Z : Matrix Q Q ℤ :=
  !![-1, -1, -1, 1;
     -1, -1, 1, -1;
     -1, 1, -1, -1;
     1, -1, -1, -1]

/-- Repeat each entry of `Y` across a block of 166 columns. -/
def Y_tilde : Matrix Q (Q × C) ℤ := fun i j => Y i j.1

/-- Repeat each entry of `Z` across a block of 166 rows. -/
def Z_tilde : Matrix (Q × C) Q ℤ := fun i j => Z i.1 j

/-- Adjoin the four border rows and columns to `M`. -/
def H_blocks : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ :=
  Matrix.fromBlocks X Y_tilde Z_tilde M

def indexEquiv : (Q ⊕ (Q × C)) ≃ Fin 668 :=
  (Equiv.sumCongr (Equiv.refl Q) finProdFinEquiv).trans finSumFinEquiv

/-- The order-668 integer matrix constructed above. -/
def H : Matrix (Fin 668) (Fin 668) ℤ :=
  Matrix.reindex indexEquiv indexEquiv H_blocks

end Hadamard

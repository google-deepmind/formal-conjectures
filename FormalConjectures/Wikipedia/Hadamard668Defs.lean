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
`seedBits`. For a sequence $x$, define $\operatorname{circ}(x)_{ij}=x_{i-j}$, and let $R$ be the
permutation matrix for $i\mapsto-i$. Write $A=\operatorname{circ}(a),\ldots,
D=\operatorname{circ}(d)$. These matrices form the $664\times664$ core

$$
G=\begin{pmatrix}
A&BR&CR&DR\\
-BR&A&D^\mathsf{T}R&-C^\mathsf{T}R\\
-CR&-D^\mathsf{T}R&A&B^\mathsf{T}R\\
-DR&C^\mathsf{T}R&-B^\mathsf{T}R&A
\end{pmatrix}.
$$

Let $Z,T,L$ be the fixed $4\times4$ matrices defined below. Repeating each entry of $T$ and $L$
across 166 positions gives matrices $\widetilde T$ of size $4\times664$ and $\widetilde L$ of size
$664\times4$. The final matrix is

$$
H=\begin{pmatrix}Z&\widetilde T\\\widetilde L&G\end{pmatrix},
\qquad \dim H=4+4\cdot166=668.
$$

## Why it works

With indices taken modulo 166, the four sequences satisfy

$$
P(t)=\sum_i(a_i a_{i+t}+b_i b_{i+t}+c_i c_{i+t}+d_i d_{i+t})
=\begin{cases}664,&t=0,\\-4,&t\ne0.\end{cases}
$$

Writing $J_{166}$ for the all-ones matrix, the diagonal $166\times166$ blocks of
$G^\mathsf{T}G$ are $668I_{166}-4J_{166}$, while its other blocks vanish. The border supplies the
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
def seedBits : Q → BitVec 166 :=
  ![0x125953fe2c4fbd9e46d5424b2a5fc58e084c372557#166,
    0x383e32a915b5fb694a447f07c65522b4c092deb770#166,
    0x71876112ff7760ef2e578e30ec225fd913e21a350#166,
    0x14c464e997f8fcd16f35c2988c8d32fce065d21947#166]

/-- Decode one entry of a stored sequence as the integer $+1$ or $-1$. -/
def seed (q : Q) (i : C) : ℤ := if (seedBits q).getLsb i then 1 else -1

/-- The permutation matrix $R$ for the map $i \mapsto -i$ on $\mathbb Z/166\mathbb Z$. -/
def rev : Matrix C C ℤ := (Equiv.neg C).permMatrix ℤ

/-- The circulant matrix $C(x)$ with entries $C(x)_{ij}=x_{i-j}$. -/
def circ (x : C → ℤ) : Matrix C C ℤ := Matrix.circulant x

/-- The $4\times4$ block array defining the $664\times664$ core matrix. -/
def gsBlocks (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := circ a
  let B := circ b
  let C := circ c
  let D := circ d
  !![A, B * rev, C * rev, D * rev;
     -(B * rev), A, D.transpose * rev, -(C.transpose * rev);
     -(C * rev), -(D.transpose * rev), A, B.transpose * rev;
     -(D * rev), C.transpose * rev, -(B.transpose * rev), A]

def gsBlocksT (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := circ a
  let B := circ b
  let C := circ c
  let D := circ d
  !![A.transpose, -(B * rev), -(C * rev), -(D * rev);
     B * rev, A.transpose, -(D.transpose * rev), C.transpose * rev;
     C * rev, D.transpose * rev, A.transpose, -(B.transpose * rev);
     D * rev, -(C.transpose * rev), B.transpose * rev, A.transpose]

/-- The $(q,r)$ block of the Gram matrix of `gsBlocks`. -/
def blockGram (a b c d : C → ℤ) (q r : Q) : Matrix C C ℤ :=
  ∑ p : Q, (gsBlocks a b c d p q).transpose * gsBlocks a b c d p r

/-- The sum of the four circulant Gram matrices. -/
def autoSum (a b c d : C → ℤ) : Matrix C C ℤ :=
  (circ a).transpose * circ a + (circ b).transpose * circ b +
    (circ c).transpose * circ c + (circ d).transpose * circ d

def gsBlockSums (sa sb sc sd : ℤ) : Matrix Q Q ℤ :=
  !![sa, sb, sc, sd;
     -sb, sa, sd, -sc;
     -sc, -sd, sa, sb;
     -sd, sc, -sb, sa]

/-- The $4\times4$ block array flattened into a $664\times664$ matrix. -/
def coreMatrix : Matrix (Q × C) (Q × C) ℤ := fun i j =>
  gsBlocks (seed 0) (seed 1) (seed 2) (seed 3) i.1 j.1 i.2 j.2

/-- The fixed $4\times4$ northwest block $Z$. -/
def border : Matrix Q Q ℤ :=
  !![-1, 1, 1, -1;
      1, -1, 1, -1;
      1, 1, -1, -1;
      -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $T$ for the top-right block. -/
def top : Matrix Q Q ℤ :=
  !![1, -1, -1, 1;
     1, -1, 1, -1;
     1, 1, -1, -1;
     -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $L$ for the bottom-left block. -/
def left : Matrix Q Q ℤ :=
  !![-1, -1, -1, 1;
     -1, -1, 1, -1;
     -1, 1, -1, -1;
     1, -1, -1, -1]

/-- Repeat each entry of `top` across a block of 166 columns. -/
def topExpanded : Matrix Q (Q × C) ℤ := fun i j => top i j.1

/-- Repeat each entry of `left` across a block of 166 rows. -/
def leftExpanded : Matrix (Q × C) Q ℤ := fun i j => left i.1 j

/-- Add the four border rows and columns to `coreMatrix`. -/
def borderedMatrix : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ :=
  Matrix.fromBlocks border topExpanded leftExpanded coreMatrix

def indexEquiv : (Q ⊕ (Q × C)) ≃ Fin 668 :=
  (Equiv.sumCongr (Equiv.refl Q) finProdFinEquiv).trans finSumFinEquiv

/-- The resulting order-668 integer matrix, indexed by `Fin 668`. -/
def H668Int : Matrix (Fin 668) (Fin 668) ℤ :=
  Matrix.reindex indexEquiv indexEquiv borderedMatrix

-- Auxiliary definitions

/-- The dot product of a sign sequence with its cyclic shift by $t$. -/
def periodicCorrelation (x : C → ℤ) (t : C) : ℤ :=
  ∑ i : C, x i * x (i + t)

/-- The sum of the periodic autocorrelations of four sequences. -/
def autoKernel (a b c d : C → ℤ) : C → ℤ :=
  fun t => periodicCorrelation a t + periodicCorrelation b t +
    periodicCorrelation c t + periodicCorrelation d t

/-- The total periodic autocorrelation of the four stored sequences. -/
def totalCorrelation (t : C) : ℤ :=
  ∑ q : Q, periodicCorrelation (seed q) t

def IsSign (z : ℤ) : Prop := z = 1 ∨ z = -1

end Hadamard

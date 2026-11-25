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
# Ulyanov's Rearrangement question

Given a continuous periodic function $f:\mathbb{T}\to\mathbb{C}$, is there a permutation
$\sigma:\mathbb{Z}\to\mathbb{Z}$ such that the rearrangement of the partial sum of the Fourier
series of $f$ given by $S_{N,\sigma}f(x) = \sum_{|n|\le N} \widehat{f}(\sigma(n))e^{2\pi i
\sigma(n)x}$ converges uniformly to $f$.

*Reference:*
[U64](https://iopscience.iop.org/article/10.1070/RM1964v019n01ABEH004136/meta) Original source
of the question (p. 51)
[arXiv:1809.08217](https://arxiv.org/pdf/1809.08217) (Problem 1)
-/

@[expose] public section

namespace UlyanovRearrangement

/--
Given a sequence of functions $\{f_n :\alpha\to\mathbb{C}\}_{n\in\mathbb{Z}}$, we have that its
rearranged sequence by a permutation $\sigma :\mathbb{Z}\to\mathbb{Z}$ is given by $f_{\sigma(n)}$.
Its rearranged partial symmetric sums are then given by $S_{a,N} = \sum_{|n|\le N} a_{\sigma(n)}.$
-/
noncomputable def partialSymmetricRearrangedSums {α : Type} (f : ℤ → α → ℂ) (σ : Equiv.Perm ℤ)
    (N : ℕ) :=
    ∑ n : Finset.Icc (-(N:ℤ)) N, f (σ n)

/--
Now, we define the partial symmetric rearranged fourier sums as the partial symmetric rearranged
sums of the sequence $\{\widehat{f}(n) e^{2\pi inx}\}_{n\in\mathbb{Z}}$.
-/
noncomputable def partialSymmetricRearrangedFourierSums
    (f : C(AddCircle (1:ℝ), ℂ)) (σ : Equiv.Perm ℤ) (N : ℕ)  : AddCircle (1:ℝ) → ℂ :=
    partialSymmetricRearrangedSums (fun n => fun x =>
    (fourierCoeff f n) * (fourier n x)) σ N

/--
Given a continuous periodic function $f:\mathbb{T}\to\mathbb{C}$, is there a permutation
$\sigma:\mathbb{Z}\to\mathbb{Z}$ such that the rearrangement of the partial sum of the Fourier
series of $f$ given by $S_{N,\sigma}f(x) = \sum_{|n|\le N} \widehat{f}(\sigma(n))e^{2\pi i
\sigma(n)x}$ converges uniformly to $f$.
-/
@[category research open, question, AMS 42]
theorem UlyanovRearrangementQuestion :
    ∀ f : C(AddCircle 1, ℂ), ∃ σ : Equiv.Perm ℤ,
    TendstoUniformly (partialSymmetricRearrangedFourierSums f σ) f Filter.atTop := by sorry

end UlyanovRearrangement

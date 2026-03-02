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

import FormalConjectures.Util.ProblemImports
import FormalConjecturesForMathlib.NumberTheory.CoveringSystem

/-!
# Erdős Problem 273

*Reference:* [erdosproblems.com/273](https://www.erdosproblems.com/273)
-/

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Pointwise

namespace Erdos273

def mods : Fin 12 → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | 4 => 12
  | 5 => 18
  | 6 => 30
  | 7 => 36
  | 8 => 40
  | 9 => 60
  | 10 => 72
  | 11 => 180

def rems : Fin 12 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 6
  | 4 => 10
  | 5 => 2
  | 6 => 14
  | 7 => 26
  | 8 => 38
  | 9 => 50
  | 10 => 50
  | 11 => 122

def primes : Fin 12 → ℕ
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 19
  | 6 => 31
  | 7 => 37
  | 8 => 41
  | 9 => 61
  | 10 => 73
  | 11 => 181

set_option maxRecDepth 200000

lemma primes_valid (i : Fin 12) : (primes i).Prime ∧ 3 ≤ primes i ∧ mods i = primes i - 1 := by
  revert i
  exact fun i => match i with
  | 0 => by
    have h1 : (3 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 1 => by
    have h1 : (5 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 2 => by
    have h1 : (7 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 3 => by
    have h1 : (11 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 4 => by
    have h1 : (13 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 5 => by
    have h1 : (19 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 6 => by
    have h1 : (31 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 7 => by
    have h1 : (37 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 8 => by
    have h1 : (41 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 9 => by
    have h1 : (61 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 10 => by
    have h1 : (73 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩
  | 11 => by
    have h1 : (181 : ℕ).Prime := by decide
    exact ⟨h1, by decide, rfl⟩

lemma mods_inj : Function.Injective mods := by
  intro i j
  revert i j
  exact fun i j => match i, j with
  | 0, 0 => fun _ => rfl
  | 0, 1 => fun h => by contradiction
  | 0, 2 => fun h => by contradiction
  | 0, 3 => fun h => by contradiction
  | 0, 4 => fun h => by contradiction
  | 0, 5 => fun h => by contradiction
  | 0, 6 => fun h => by contradiction
  | 0, 7 => fun h => by contradiction
  | 0, 8 => fun h => by contradiction
  | 0, 9 => fun h => by contradiction
  | 0, 10 => fun h => by contradiction
  | 0, 11 => fun h => by contradiction
  | 1, 0 => fun h => by contradiction
  | 1, 1 => fun _ => rfl
  | 1, 2 => fun h => by contradiction
  | 1, 3 => fun h => by contradiction
  | 1, 4 => fun h => by contradiction
  | 1, 5 => fun h => by contradiction
  | 1, 6 => fun h => by contradiction
  | 1, 7 => fun h => by contradiction
  | 1, 8 => fun h => by contradiction
  | 1, 9 => fun h => by contradiction
  | 1, 10 => fun h => by contradiction
  | 1, 11 => fun h => by contradiction
  | 2, 0 => fun h => by contradiction
  | 2, 1 => fun h => by contradiction
  | 2, 2 => fun _ => rfl
  | 2, 3 => fun h => by contradiction
  | 2, 4 => fun h => by contradiction
  | 2, 5 => fun h => by contradiction
  | 2, 6 => fun h => by contradiction
  | 2, 7 => fun h => by contradiction
  | 2, 8 => fun h => by contradiction
  | 2, 9 => fun h => by contradiction
  | 2, 10 => fun h => by contradiction
  | 2, 11 => fun h => by contradiction
  | 3, 0 => fun h => by contradiction
  | 3, 1 => fun h => by contradiction
  | 3, 2 => fun h => by contradiction
  | 3, 3 => fun _ => rfl
  | 3, 4 => fun h => by contradiction
  | 3, 5 => fun h => by contradiction
  | 3, 6 => fun h => by contradiction
  | 3, 7 => fun h => by contradiction
  | 3, 8 => fun h => by contradiction
  | 3, 9 => fun h => by contradiction
  | 3, 10 => fun h => by contradiction
  | 3, 11 => fun h => by contradiction
  | 4, 0 => fun h => by contradiction
  | 4, 1 => fun h => by contradiction
  | 4, 2 => fun h => by contradiction
  | 4, 3 => fun h => by contradiction
  | 4, 4 => fun _ => rfl
  | 4, 5 => fun h => by contradiction
  | 4, 6 => fun h => by contradiction
  | 4, 7 => fun h => by contradiction
  | 4, 8 => fun h => by contradiction
  | 4, 9 => fun h => by contradiction
  | 4, 10 => fun h => by contradiction
  | 4, 11 => fun h => by contradiction
  | 5, 0 => fun h => by contradiction
  | 5, 1 => fun h => by contradiction
  | 5, 2 => fun h => by contradiction
  | 5, 3 => fun h => by contradiction
  | 5, 4 => fun h => by contradiction
  | 5, 5 => fun _ => rfl
  | 5, 6 => fun h => by contradiction
  | 5, 7 => fun h => by contradiction
  | 5, 8 => fun h => by contradiction
  | 5, 9 => fun h => by contradiction
  | 5, 10 => fun h => by contradiction
  | 5, 11 => fun h => by contradiction
  | 6, 0 => fun h => by contradiction
  | 6, 1 => fun h => by contradiction
  | 6, 2 => fun h => by contradiction
  | 6, 3 => fun h => by contradiction
  | 6, 4 => fun h => by contradiction
  | 6, 5 => fun h => by contradiction
  | 6, 6 => fun _ => rfl
  | 6, 7 => fun h => by contradiction
  | 6, 8 => fun h => by contradiction
  | 6, 9 => fun h => by contradiction
  | 6, 10 => fun h => by contradiction
  | 6, 11 => fun h => by contradiction
  | 7, 0 => fun h => by contradiction
  | 7, 1 => fun h => by contradiction
  | 7, 2 => fun h => by contradiction
  | 7, 3 => fun h => by contradiction
  | 7, 4 => fun h => by contradiction
  | 7, 5 => fun h => by contradiction
  | 7, 6 => fun h => by contradiction
  | 7, 7 => fun _ => rfl
  | 7, 8 => fun h => by contradiction
  | 7, 9 => fun h => by contradiction
  | 7, 10 => fun h => by contradiction
  | 7, 11 => fun h => by contradiction
  | 8, 0 => fun h => by contradiction
  | 8, 1 => fun h => by contradiction
  | 8, 2 => fun h => by contradiction
  | 8, 3 => fun h => by contradiction
  | 8, 4 => fun h => by contradiction
  | 8, 5 => fun h => by contradiction
  | 8, 6 => fun h => by contradiction
  | 8, 7 => fun h => by contradiction
  | 8, 8 => fun _ => rfl
  | 8, 9 => fun h => by contradiction
  | 8, 10 => fun h => by contradiction
  | 8, 11 => fun h => by contradiction
  | 9, 0 => fun h => by contradiction
  | 9, 1 => fun h => by contradiction
  | 9, 2 => fun h => by contradiction
  | 9, 3 => fun h => by contradiction
  | 9, 4 => fun h => by contradiction
  | 9, 5 => fun h => by contradiction
  | 9, 6 => fun h => by contradiction
  | 9, 7 => fun h => by contradiction
  | 9, 8 => fun h => by contradiction
  | 9, 9 => fun _ => rfl
  | 9, 10 => fun h => by contradiction
  | 9, 11 => fun h => by contradiction
  | 10, 0 => fun h => by contradiction
  | 10, 1 => fun h => by contradiction
  | 10, 2 => fun h => by contradiction
  | 10, 3 => fun h => by contradiction
  | 10, 4 => fun h => by contradiction
  | 10, 5 => fun h => by contradiction
  | 10, 6 => fun h => by contradiction
  | 10, 7 => fun h => by contradiction
  | 10, 8 => fun h => by contradiction
  | 10, 9 => fun h => by contradiction
  | 10, 10 => fun _ => rfl
  | 10, 11 => fun h => by contradiction
  | 11, 0 => fun h => by contradiction
  | 11, 1 => fun h => by contradiction
  | 11, 2 => fun h => by contradiction
  | 11, 3 => fun h => by contradiction
  | 11, 4 => fun h => by contradiction
  | 11, 5 => fun h => by contradiction
  | 11, 6 => fun h => by contradiction
  | 11, 7 => fun h => by contradiction
  | 11, 8 => fun h => by contradiction
  | 11, 9 => fun h => by contradiction
  | 11, 10 => fun h => by contradiction
  | 11, 11 => fun _ => rfl

lemma mods_pos (i : Fin 12) : 0 < mods i := by
  revert i
  exact fun i => match i with
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | 6 => by decide
  | 7 => by decide
  | 8 => by decide
  | 9 => by decide
  | 10 => by decide
  | 11 => by decide

lemma mods_not_bot (i : Fin 12) : Ideal.span {(mods i : ℕ)} ≠ ⊥ := by
  intro h
  have h_mem : mods i ∈ Ideal.span {(mods i : ℕ)} := Ideal.subset_span (Set.mem_singleton _)
  rw [h] at h_mem
  have h0 : mods i = 0 := h_mem
  have hpos := mods_pos i
  omega

lemma mods_dvd_360 (i : Fin 12) : mods i ∣ 360 := by
  revert i
  exact fun i => match i with
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | 6 => by decide
  | 7 => by decide
  | 8 => by decide
  | 9 => by decide
  | 10 => by decide
  | 11 => by decide
lemma cover_lemma_0 : 0 % mods 1 = rems 1 := rfl
lemma cover_lemma_1 : 1 % mods 0 = rems 0 := rfl
lemma cover_lemma_2 : 2 % mods 5 = rems 5 := rfl
lemma cover_lemma_3 : 3 % mods 0 = rems 0 := rfl
lemma cover_lemma_4 : 4 % mods 1 = rems 1 := rfl
lemma cover_lemma_5 : 5 % mods 0 = rems 0 := rfl
lemma cover_lemma_6 : 6 % mods 2 = rems 2 := rfl
lemma cover_lemma_7 : 7 % mods 0 = rems 0 := rfl
lemma cover_lemma_8 : 8 % mods 1 = rems 1 := rfl
lemma cover_lemma_9 : 9 % mods 0 = rems 0 := rfl
lemma cover_lemma_10 : 10 % mods 4 = rems 4 := rfl
lemma cover_lemma_11 : 11 % mods 0 = rems 0 := rfl
lemma cover_lemma_12 : 12 % mods 1 = rems 1 := rfl
lemma cover_lemma_13 : 13 % mods 0 = rems 0 := rfl
lemma cover_lemma_14 : 14 % mods 6 = rems 6 := rfl
lemma cover_lemma_15 : 15 % mods 0 = rems 0 := rfl
lemma cover_lemma_16 : 16 % mods 1 = rems 1 := rfl
lemma cover_lemma_17 : 17 % mods 0 = rems 0 := rfl
lemma cover_lemma_18 : 18 % mods 2 = rems 2 := rfl
lemma cover_lemma_19 : 19 % mods 0 = rems 0 := rfl
lemma cover_lemma_20 : 20 % mods 1 = rems 1 := rfl
lemma cover_lemma_21 : 21 % mods 0 = rems 0 := rfl
lemma cover_lemma_22 : 22 % mods 4 = rems 4 := rfl
lemma cover_lemma_23 : 23 % mods 0 = rems 0 := rfl
lemma cover_lemma_24 : 24 % mods 1 = rems 1 := rfl
lemma cover_lemma_25 : 25 % mods 0 = rems 0 := rfl
lemma cover_lemma_26 : 26 % mods 3 = rems 3 := rfl
lemma cover_lemma_27 : 27 % mods 0 = rems 0 := rfl
lemma cover_lemma_28 : 28 % mods 1 = rems 1 := rfl
lemma cover_lemma_29 : 29 % mods 0 = rems 0 := rfl
lemma cover_lemma_30 : 30 % mods 2 = rems 2 := rfl
lemma cover_lemma_31 : 31 % mods 0 = rems 0 := rfl
lemma cover_lemma_32 : 32 % mods 1 = rems 1 := rfl
lemma cover_lemma_33 : 33 % mods 0 = rems 0 := rfl
lemma cover_lemma_34 : 34 % mods 4 = rems 4 := rfl
lemma cover_lemma_35 : 35 % mods 0 = rems 0 := rfl
lemma cover_lemma_36 : 36 % mods 1 = rems 1 := rfl
lemma cover_lemma_37 : 37 % mods 0 = rems 0 := rfl
lemma cover_lemma_38 : 38 % mods 5 = rems 5 := rfl
lemma cover_lemma_39 : 39 % mods 0 = rems 0 := rfl
lemma cover_lemma_40 : 40 % mods 1 = rems 1 := rfl
lemma cover_lemma_41 : 41 % mods 0 = rems 0 := rfl
lemma cover_lemma_42 : 42 % mods 2 = rems 2 := rfl
lemma cover_lemma_43 : 43 % mods 0 = rems 0 := rfl
lemma cover_lemma_44 : 44 % mods 1 = rems 1 := rfl
lemma cover_lemma_45 : 45 % mods 0 = rems 0 := rfl
lemma cover_lemma_46 : 46 % mods 3 = rems 3 := rfl
lemma cover_lemma_47 : 47 % mods 0 = rems 0 := rfl
lemma cover_lemma_48 : 48 % mods 1 = rems 1 := rfl
lemma cover_lemma_49 : 49 % mods 0 = rems 0 := rfl
lemma cover_lemma_50 : 50 % mods 9 = rems 9 := rfl
lemma cover_lemma_51 : 51 % mods 0 = rems 0 := rfl
lemma cover_lemma_52 : 52 % mods 1 = rems 1 := rfl
lemma cover_lemma_53 : 53 % mods 0 = rems 0 := rfl
lemma cover_lemma_54 : 54 % mods 2 = rems 2 := rfl
lemma cover_lemma_55 : 55 % mods 0 = rems 0 := rfl
lemma cover_lemma_56 : 56 % mods 1 = rems 1 := rfl
lemma cover_lemma_57 : 57 % mods 0 = rems 0 := rfl
lemma cover_lemma_58 : 58 % mods 4 = rems 4 := rfl
lemma cover_lemma_59 : 59 % mods 0 = rems 0 := rfl
lemma cover_lemma_60 : 60 % mods 1 = rems 1 := rfl
lemma cover_lemma_61 : 61 % mods 0 = rems 0 := rfl
lemma cover_lemma_62 : 62 % mods 7 = rems 7 := rfl
lemma cover_lemma_63 : 63 % mods 0 = rems 0 := rfl
lemma cover_lemma_64 : 64 % mods 1 = rems 1 := rfl
lemma cover_lemma_65 : 65 % mods 0 = rems 0 := rfl
lemma cover_lemma_66 : 66 % mods 2 = rems 2 := rfl
lemma cover_lemma_67 : 67 % mods 0 = rems 0 := rfl
lemma cover_lemma_68 : 68 % mods 1 = rems 1 := rfl
lemma cover_lemma_69 : 69 % mods 0 = rems 0 := rfl
lemma cover_lemma_70 : 70 % mods 4 = rems 4 := rfl
lemma cover_lemma_71 : 71 % mods 0 = rems 0 := rfl
lemma cover_lemma_72 : 72 % mods 1 = rems 1 := rfl
lemma cover_lemma_73 : 73 % mods 0 = rems 0 := rfl
lemma cover_lemma_74 : 74 % mods 5 = rems 5 := rfl
lemma cover_lemma_75 : 75 % mods 0 = rems 0 := rfl
lemma cover_lemma_76 : 76 % mods 1 = rems 1 := rfl
lemma cover_lemma_77 : 77 % mods 0 = rems 0 := rfl
lemma cover_lemma_78 : 78 % mods 2 = rems 2 := rfl
lemma cover_lemma_79 : 79 % mods 0 = rems 0 := rfl
lemma cover_lemma_80 : 80 % mods 1 = rems 1 := rfl
lemma cover_lemma_81 : 81 % mods 0 = rems 0 := rfl
lemma cover_lemma_82 : 82 % mods 4 = rems 4 := rfl
lemma cover_lemma_83 : 83 % mods 0 = rems 0 := rfl
lemma cover_lemma_84 : 84 % mods 1 = rems 1 := rfl
lemma cover_lemma_85 : 85 % mods 0 = rems 0 := rfl
lemma cover_lemma_86 : 86 % mods 3 = rems 3 := rfl
lemma cover_lemma_87 : 87 % mods 0 = rems 0 := rfl
lemma cover_lemma_88 : 88 % mods 1 = rems 1 := rfl
lemma cover_lemma_89 : 89 % mods 0 = rems 0 := rfl
lemma cover_lemma_90 : 90 % mods 2 = rems 2 := rfl
lemma cover_lemma_91 : 91 % mods 0 = rems 0 := rfl
lemma cover_lemma_92 : 92 % mods 1 = rems 1 := rfl
lemma cover_lemma_93 : 93 % mods 0 = rems 0 := rfl
lemma cover_lemma_94 : 94 % mods 4 = rems 4 := rfl
lemma cover_lemma_95 : 95 % mods 0 = rems 0 := rfl
lemma cover_lemma_96 : 96 % mods 1 = rems 1 := rfl
lemma cover_lemma_97 : 97 % mods 0 = rems 0 := rfl
lemma cover_lemma_98 : 98 % mods 7 = rems 7 := rfl
lemma cover_lemma_99 : 99 % mods 0 = rems 0 := rfl
lemma cover_lemma_100 : 100 % mods 1 = rems 1 := rfl
lemma cover_lemma_101 : 101 % mods 0 = rems 0 := rfl
lemma cover_lemma_102 : 102 % mods 2 = rems 2 := rfl
lemma cover_lemma_103 : 103 % mods 0 = rems 0 := rfl
lemma cover_lemma_104 : 104 % mods 1 = rems 1 := rfl
lemma cover_lemma_105 : 105 % mods 0 = rems 0 := rfl
lemma cover_lemma_106 : 106 % mods 3 = rems 3 := rfl
lemma cover_lemma_107 : 107 % mods 0 = rems 0 := rfl
lemma cover_lemma_108 : 108 % mods 1 = rems 1 := rfl
lemma cover_lemma_109 : 109 % mods 0 = rems 0 := rfl
lemma cover_lemma_110 : 110 % mods 5 = rems 5 := rfl
lemma cover_lemma_111 : 111 % mods 0 = rems 0 := rfl
lemma cover_lemma_112 : 112 % mods 1 = rems 1 := rfl
lemma cover_lemma_113 : 113 % mods 0 = rems 0 := rfl
lemma cover_lemma_114 : 114 % mods 2 = rems 2 := rfl
lemma cover_lemma_115 : 115 % mods 0 = rems 0 := rfl
lemma cover_lemma_116 : 116 % mods 1 = rems 1 := rfl
lemma cover_lemma_117 : 117 % mods 0 = rems 0 := rfl
lemma cover_lemma_118 : 118 % mods 4 = rems 4 := rfl
lemma cover_lemma_119 : 119 % mods 0 = rems 0 := rfl
lemma cover_lemma_120 : 120 % mods 1 = rems 1 := rfl
lemma cover_lemma_121 : 121 % mods 0 = rems 0 := rfl
lemma cover_lemma_122 : 122 % mods 10 = rems 10 := rfl
lemma cover_lemma_123 : 123 % mods 0 = rems 0 := rfl
lemma cover_lemma_124 : 124 % mods 1 = rems 1 := rfl
lemma cover_lemma_125 : 125 % mods 0 = rems 0 := rfl
lemma cover_lemma_126 : 126 % mods 2 = rems 2 := rfl
lemma cover_lemma_127 : 127 % mods 0 = rems 0 := rfl
lemma cover_lemma_128 : 128 % mods 1 = rems 1 := rfl
lemma cover_lemma_129 : 129 % mods 0 = rems 0 := rfl
lemma cover_lemma_130 : 130 % mods 4 = rems 4 := rfl
lemma cover_lemma_131 : 131 % mods 0 = rems 0 := rfl
lemma cover_lemma_132 : 132 % mods 1 = rems 1 := rfl
lemma cover_lemma_133 : 133 % mods 0 = rems 0 := rfl
lemma cover_lemma_134 : 134 % mods 6 = rems 6 := rfl
lemma cover_lemma_135 : 135 % mods 0 = rems 0 := rfl
lemma cover_lemma_136 : 136 % mods 1 = rems 1 := rfl
lemma cover_lemma_137 : 137 % mods 0 = rems 0 := rfl
lemma cover_lemma_138 : 138 % mods 2 = rems 2 := rfl
lemma cover_lemma_139 : 139 % mods 0 = rems 0 := rfl
lemma cover_lemma_140 : 140 % mods 1 = rems 1 := rfl
lemma cover_lemma_141 : 141 % mods 0 = rems 0 := rfl
lemma cover_lemma_142 : 142 % mods 4 = rems 4 := rfl
lemma cover_lemma_143 : 143 % mods 0 = rems 0 := rfl
lemma cover_lemma_144 : 144 % mods 1 = rems 1 := rfl
lemma cover_lemma_145 : 145 % mods 0 = rems 0 := rfl
lemma cover_lemma_146 : 146 % mods 3 = rems 3 := rfl
lemma cover_lemma_147 : 147 % mods 0 = rems 0 := rfl
lemma cover_lemma_148 : 148 % mods 1 = rems 1 := rfl
lemma cover_lemma_149 : 149 % mods 0 = rems 0 := rfl
lemma cover_lemma_150 : 150 % mods 2 = rems 2 := rfl
lemma cover_lemma_151 : 151 % mods 0 = rems 0 := rfl
lemma cover_lemma_152 : 152 % mods 1 = rems 1 := rfl
lemma cover_lemma_153 : 153 % mods 0 = rems 0 := rfl
lemma cover_lemma_154 : 154 % mods 4 = rems 4 := rfl
lemma cover_lemma_155 : 155 % mods 0 = rems 0 := rfl
lemma cover_lemma_156 : 156 % mods 1 = rems 1 := rfl
lemma cover_lemma_157 : 157 % mods 0 = rems 0 := rfl
lemma cover_lemma_158 : 158 % mods 8 = rems 8 := rfl
lemma cover_lemma_159 : 159 % mods 0 = rems 0 := rfl
lemma cover_lemma_160 : 160 % mods 1 = rems 1 := rfl
lemma cover_lemma_161 : 161 % mods 0 = rems 0 := rfl
lemma cover_lemma_162 : 162 % mods 2 = rems 2 := rfl
lemma cover_lemma_163 : 163 % mods 0 = rems 0 := rfl
lemma cover_lemma_164 : 164 % mods 1 = rems 1 := rfl
lemma cover_lemma_165 : 165 % mods 0 = rems 0 := rfl
lemma cover_lemma_166 : 166 % mods 3 = rems 3 := rfl
lemma cover_lemma_167 : 167 % mods 0 = rems 0 := rfl
lemma cover_lemma_168 : 168 % mods 1 = rems 1 := rfl
lemma cover_lemma_169 : 169 % mods 0 = rems 0 := rfl
lemma cover_lemma_170 : 170 % mods 7 = rems 7 := rfl
lemma cover_lemma_171 : 171 % mods 0 = rems 0 := rfl
lemma cover_lemma_172 : 172 % mods 1 = rems 1 := rfl
lemma cover_lemma_173 : 173 % mods 0 = rems 0 := rfl
lemma cover_lemma_174 : 174 % mods 2 = rems 2 := rfl
lemma cover_lemma_175 : 175 % mods 0 = rems 0 := rfl
lemma cover_lemma_176 : 176 % mods 1 = rems 1 := rfl
lemma cover_lemma_177 : 177 % mods 0 = rems 0 := rfl
lemma cover_lemma_178 : 178 % mods 4 = rems 4 := rfl
lemma cover_lemma_179 : 179 % mods 0 = rems 0 := rfl
lemma cover_lemma_180 : 180 % mods 1 = rems 1 := rfl
lemma cover_lemma_181 : 181 % mods 0 = rems 0 := rfl
lemma cover_lemma_182 : 182 % mods 5 = rems 5 := rfl
lemma cover_lemma_183 : 183 % mods 0 = rems 0 := rfl
lemma cover_lemma_184 : 184 % mods 1 = rems 1 := rfl
lemma cover_lemma_185 : 185 % mods 0 = rems 0 := rfl
lemma cover_lemma_186 : 186 % mods 2 = rems 2 := rfl
lemma cover_lemma_187 : 187 % mods 0 = rems 0 := rfl
lemma cover_lemma_188 : 188 % mods 1 = rems 1 := rfl
lemma cover_lemma_189 : 189 % mods 0 = rems 0 := rfl
lemma cover_lemma_190 : 190 % mods 4 = rems 4 := rfl
lemma cover_lemma_191 : 191 % mods 0 = rems 0 := rfl
lemma cover_lemma_192 : 192 % mods 1 = rems 1 := rfl
lemma cover_lemma_193 : 193 % mods 0 = rems 0 := rfl
lemma cover_lemma_194 : 194 % mods 6 = rems 6 := rfl
lemma cover_lemma_195 : 195 % mods 0 = rems 0 := rfl
lemma cover_lemma_196 : 196 % mods 1 = rems 1 := rfl
lemma cover_lemma_197 : 197 % mods 0 = rems 0 := rfl
lemma cover_lemma_198 : 198 % mods 2 = rems 2 := rfl
lemma cover_lemma_199 : 199 % mods 0 = rems 0 := rfl
lemma cover_lemma_200 : 200 % mods 1 = rems 1 := rfl
lemma cover_lemma_201 : 201 % mods 0 = rems 0 := rfl
lemma cover_lemma_202 : 202 % mods 4 = rems 4 := rfl
lemma cover_lemma_203 : 203 % mods 0 = rems 0 := rfl
lemma cover_lemma_204 : 204 % mods 1 = rems 1 := rfl
lemma cover_lemma_205 : 205 % mods 0 = rems 0 := rfl
lemma cover_lemma_206 : 206 % mods 3 = rems 3 := rfl
lemma cover_lemma_207 : 207 % mods 0 = rems 0 := rfl
lemma cover_lemma_208 : 208 % mods 1 = rems 1 := rfl
lemma cover_lemma_209 : 209 % mods 0 = rems 0 := rfl
lemma cover_lemma_210 : 210 % mods 2 = rems 2 := rfl
lemma cover_lemma_211 : 211 % mods 0 = rems 0 := rfl
lemma cover_lemma_212 : 212 % mods 1 = rems 1 := rfl
lemma cover_lemma_213 : 213 % mods 0 = rems 0 := rfl
lemma cover_lemma_214 : 214 % mods 4 = rems 4 := rfl
lemma cover_lemma_215 : 215 % mods 0 = rems 0 := rfl
lemma cover_lemma_216 : 216 % mods 1 = rems 1 := rfl
lemma cover_lemma_217 : 217 % mods 0 = rems 0 := rfl
lemma cover_lemma_218 : 218 % mods 5 = rems 5 := rfl
lemma cover_lemma_219 : 219 % mods 0 = rems 0 := rfl
lemma cover_lemma_220 : 220 % mods 1 = rems 1 := rfl
lemma cover_lemma_221 : 221 % mods 0 = rems 0 := rfl
lemma cover_lemma_222 : 222 % mods 2 = rems 2 := rfl
lemma cover_lemma_223 : 223 % mods 0 = rems 0 := rfl
lemma cover_lemma_224 : 224 % mods 1 = rems 1 := rfl
lemma cover_lemma_225 : 225 % mods 0 = rems 0 := rfl
lemma cover_lemma_226 : 226 % mods 3 = rems 3 := rfl
lemma cover_lemma_227 : 227 % mods 0 = rems 0 := rfl
lemma cover_lemma_228 : 228 % mods 1 = rems 1 := rfl
lemma cover_lemma_229 : 229 % mods 0 = rems 0 := rfl
lemma cover_lemma_230 : 230 % mods 9 = rems 9 := rfl
lemma cover_lemma_231 : 231 % mods 0 = rems 0 := rfl
lemma cover_lemma_232 : 232 % mods 1 = rems 1 := rfl
lemma cover_lemma_233 : 233 % mods 0 = rems 0 := rfl
lemma cover_lemma_234 : 234 % mods 2 = rems 2 := rfl
lemma cover_lemma_235 : 235 % mods 0 = rems 0 := rfl
lemma cover_lemma_236 : 236 % mods 1 = rems 1 := rfl
lemma cover_lemma_237 : 237 % mods 0 = rems 0 := rfl
lemma cover_lemma_238 : 238 % mods 4 = rems 4 := rfl
lemma cover_lemma_239 : 239 % mods 0 = rems 0 := rfl
lemma cover_lemma_240 : 240 % mods 1 = rems 1 := rfl
lemma cover_lemma_241 : 241 % mods 0 = rems 0 := rfl
lemma cover_lemma_242 : 242 % mods 7 = rems 7 := rfl
lemma cover_lemma_243 : 243 % mods 0 = rems 0 := rfl
lemma cover_lemma_244 : 244 % mods 1 = rems 1 := rfl
lemma cover_lemma_245 : 245 % mods 0 = rems 0 := rfl
lemma cover_lemma_246 : 246 % mods 2 = rems 2 := rfl
lemma cover_lemma_247 : 247 % mods 0 = rems 0 := rfl
lemma cover_lemma_248 : 248 % mods 1 = rems 1 := rfl
lemma cover_lemma_249 : 249 % mods 0 = rems 0 := rfl
lemma cover_lemma_250 : 250 % mods 4 = rems 4 := rfl
lemma cover_lemma_251 : 251 % mods 0 = rems 0 := rfl
lemma cover_lemma_252 : 252 % mods 1 = rems 1 := rfl
lemma cover_lemma_253 : 253 % mods 0 = rems 0 := rfl
lemma cover_lemma_254 : 254 % mods 5 = rems 5 := rfl
lemma cover_lemma_255 : 255 % mods 0 = rems 0 := rfl
lemma cover_lemma_256 : 256 % mods 1 = rems 1 := rfl
lemma cover_lemma_257 : 257 % mods 0 = rems 0 := rfl
lemma cover_lemma_258 : 258 % mods 2 = rems 2 := rfl
lemma cover_lemma_259 : 259 % mods 0 = rems 0 := rfl
lemma cover_lemma_260 : 260 % mods 1 = rems 1 := rfl
lemma cover_lemma_261 : 261 % mods 0 = rems 0 := rfl
lemma cover_lemma_262 : 262 % mods 4 = rems 4 := rfl
lemma cover_lemma_263 : 263 % mods 0 = rems 0 := rfl
lemma cover_lemma_264 : 264 % mods 1 = rems 1 := rfl
lemma cover_lemma_265 : 265 % mods 0 = rems 0 := rfl
lemma cover_lemma_266 : 266 % mods 3 = rems 3 := rfl
lemma cover_lemma_267 : 267 % mods 0 = rems 0 := rfl
lemma cover_lemma_268 : 268 % mods 1 = rems 1 := rfl
lemma cover_lemma_269 : 269 % mods 0 = rems 0 := rfl
lemma cover_lemma_270 : 270 % mods 2 = rems 2 := rfl
lemma cover_lemma_271 : 271 % mods 0 = rems 0 := rfl
lemma cover_lemma_272 : 272 % mods 1 = rems 1 := rfl
lemma cover_lemma_273 : 273 % mods 0 = rems 0 := rfl
lemma cover_lemma_274 : 274 % mods 4 = rems 4 := rfl
lemma cover_lemma_275 : 275 % mods 0 = rems 0 := rfl
lemma cover_lemma_276 : 276 % mods 1 = rems 1 := rfl
lemma cover_lemma_277 : 277 % mods 0 = rems 0 := rfl
lemma cover_lemma_278 : 278 % mods 7 = rems 7 := rfl
lemma cover_lemma_279 : 279 % mods 0 = rems 0 := rfl
lemma cover_lemma_280 : 280 % mods 1 = rems 1 := rfl
lemma cover_lemma_281 : 281 % mods 0 = rems 0 := rfl
lemma cover_lemma_282 : 282 % mods 2 = rems 2 := rfl
lemma cover_lemma_283 : 283 % mods 0 = rems 0 := rfl
lemma cover_lemma_284 : 284 % mods 1 = rems 1 := rfl
lemma cover_lemma_285 : 285 % mods 0 = rems 0 := rfl
lemma cover_lemma_286 : 286 % mods 3 = rems 3 := rfl
lemma cover_lemma_287 : 287 % mods 0 = rems 0 := rfl
lemma cover_lemma_288 : 288 % mods 1 = rems 1 := rfl
lemma cover_lemma_289 : 289 % mods 0 = rems 0 := rfl
lemma cover_lemma_290 : 290 % mods 5 = rems 5 := rfl
lemma cover_lemma_291 : 291 % mods 0 = rems 0 := rfl
lemma cover_lemma_292 : 292 % mods 1 = rems 1 := rfl
lemma cover_lemma_293 : 293 % mods 0 = rems 0 := rfl
lemma cover_lemma_294 : 294 % mods 2 = rems 2 := rfl
lemma cover_lemma_295 : 295 % mods 0 = rems 0 := rfl
lemma cover_lemma_296 : 296 % mods 1 = rems 1 := rfl
lemma cover_lemma_297 : 297 % mods 0 = rems 0 := rfl
lemma cover_lemma_298 : 298 % mods 4 = rems 4 := rfl
lemma cover_lemma_299 : 299 % mods 0 = rems 0 := rfl
lemma cover_lemma_300 : 300 % mods 1 = rems 1 := rfl
lemma cover_lemma_301 : 301 % mods 0 = rems 0 := rfl
lemma cover_lemma_302 : 302 % mods 11 = rems 11 := rfl
lemma cover_lemma_303 : 303 % mods 0 = rems 0 := rfl
lemma cover_lemma_304 : 304 % mods 1 = rems 1 := rfl
lemma cover_lemma_305 : 305 % mods 0 = rems 0 := rfl
lemma cover_lemma_306 : 306 % mods 2 = rems 2 := rfl
lemma cover_lemma_307 : 307 % mods 0 = rems 0 := rfl
lemma cover_lemma_308 : 308 % mods 1 = rems 1 := rfl
lemma cover_lemma_309 : 309 % mods 0 = rems 0 := rfl
lemma cover_lemma_310 : 310 % mods 4 = rems 4 := rfl
lemma cover_lemma_311 : 311 % mods 0 = rems 0 := rfl
lemma cover_lemma_312 : 312 % mods 1 = rems 1 := rfl
lemma cover_lemma_313 : 313 % mods 0 = rems 0 := rfl
lemma cover_lemma_314 : 314 % mods 6 = rems 6 := rfl
lemma cover_lemma_315 : 315 % mods 0 = rems 0 := rfl
lemma cover_lemma_316 : 316 % mods 1 = rems 1 := rfl
lemma cover_lemma_317 : 317 % mods 0 = rems 0 := rfl
lemma cover_lemma_318 : 318 % mods 2 = rems 2 := rfl
lemma cover_lemma_319 : 319 % mods 0 = rems 0 := rfl
lemma cover_lemma_320 : 320 % mods 1 = rems 1 := rfl
lemma cover_lemma_321 : 321 % mods 0 = rems 0 := rfl
lemma cover_lemma_322 : 322 % mods 4 = rems 4 := rfl
lemma cover_lemma_323 : 323 % mods 0 = rems 0 := rfl
lemma cover_lemma_324 : 324 % mods 1 = rems 1 := rfl
lemma cover_lemma_325 : 325 % mods 0 = rems 0 := rfl
lemma cover_lemma_326 : 326 % mods 3 = rems 3 := rfl
lemma cover_lemma_327 : 327 % mods 0 = rems 0 := rfl
lemma cover_lemma_328 : 328 % mods 1 = rems 1 := rfl
lemma cover_lemma_329 : 329 % mods 0 = rems 0 := rfl
lemma cover_lemma_330 : 330 % mods 2 = rems 2 := rfl
lemma cover_lemma_331 : 331 % mods 0 = rems 0 := rfl
lemma cover_lemma_332 : 332 % mods 1 = rems 1 := rfl
lemma cover_lemma_333 : 333 % mods 0 = rems 0 := rfl
lemma cover_lemma_334 : 334 % mods 4 = rems 4 := rfl
lemma cover_lemma_335 : 335 % mods 0 = rems 0 := rfl
lemma cover_lemma_336 : 336 % mods 1 = rems 1 := rfl
lemma cover_lemma_337 : 337 % mods 0 = rems 0 := rfl
lemma cover_lemma_338 : 338 % mods 10 = rems 10 := rfl
lemma cover_lemma_339 : 339 % mods 0 = rems 0 := rfl
lemma cover_lemma_340 : 340 % mods 1 = rems 1 := rfl
lemma cover_lemma_341 : 341 % mods 0 = rems 0 := rfl
lemma cover_lemma_342 : 342 % mods 2 = rems 2 := rfl
lemma cover_lemma_343 : 343 % mods 0 = rems 0 := rfl
lemma cover_lemma_344 : 344 % mods 1 = rems 1 := rfl
lemma cover_lemma_345 : 345 % mods 0 = rems 0 := rfl
lemma cover_lemma_346 : 346 % mods 3 = rems 3 := rfl
lemma cover_lemma_347 : 347 % mods 0 = rems 0 := rfl
lemma cover_lemma_348 : 348 % mods 1 = rems 1 := rfl
lemma cover_lemma_349 : 349 % mods 0 = rems 0 := rfl
lemma cover_lemma_350 : 350 % mods 7 = rems 7 := rfl
lemma cover_lemma_351 : 351 % mods 0 = rems 0 := rfl
lemma cover_lemma_352 : 352 % mods 1 = rems 1 := rfl
lemma cover_lemma_353 : 353 % mods 0 = rems 0 := rfl
lemma cover_lemma_354 : 354 % mods 2 = rems 2 := rfl
lemma cover_lemma_355 : 355 % mods 0 = rems 0 := rfl
lemma cover_lemma_356 : 356 % mods 1 = rems 1 := rfl
lemma cover_lemma_357 : 357 % mods 0 = rems 0 := rfl
lemma cover_lemma_358 : 358 % mods 4 = rems 4 := rfl
lemma cover_lemma_359 : 359 % mods 0 = rems 0 := rfl

lemma covers_360 (x : ℕ) : ∃ i : Fin 12, x % mods i = rems i := by
  have h_mod : x % 360 < 360 := Nat.mod_lt x (by decide)
  have h_cases : ∃ i : Fin 12, (x % 360) % mods i = rems i := by
    generalize hy : x % 360 = y
    rw [hy] at h_mod
    interval_cases y
    · exact ⟨1, cover_lemma_0⟩
    · exact ⟨0, cover_lemma_1⟩
    · exact ⟨5, cover_lemma_2⟩
    · exact ⟨0, cover_lemma_3⟩
    · exact ⟨1, cover_lemma_4⟩
    · exact ⟨0, cover_lemma_5⟩
    · exact ⟨2, cover_lemma_6⟩
    · exact ⟨0, cover_lemma_7⟩
    · exact ⟨1, cover_lemma_8⟩
    · exact ⟨0, cover_lemma_9⟩
    · exact ⟨4, cover_lemma_10⟩
    · exact ⟨0, cover_lemma_11⟩
    · exact ⟨1, cover_lemma_12⟩
    · exact ⟨0, cover_lemma_13⟩
    · exact ⟨6, cover_lemma_14⟩
    · exact ⟨0, cover_lemma_15⟩
    · exact ⟨1, cover_lemma_16⟩
    · exact ⟨0, cover_lemma_17⟩
    · exact ⟨2, cover_lemma_18⟩
    · exact ⟨0, cover_lemma_19⟩
    · exact ⟨1, cover_lemma_20⟩
    · exact ⟨0, cover_lemma_21⟩
    · exact ⟨4, cover_lemma_22⟩
    · exact ⟨0, cover_lemma_23⟩
    · exact ⟨1, cover_lemma_24⟩
    · exact ⟨0, cover_lemma_25⟩
    · exact ⟨3, cover_lemma_26⟩
    · exact ⟨0, cover_lemma_27⟩
    · exact ⟨1, cover_lemma_28⟩
    · exact ⟨0, cover_lemma_29⟩
    · exact ⟨2, cover_lemma_30⟩
    · exact ⟨0, cover_lemma_31⟩
    · exact ⟨1, cover_lemma_32⟩
    · exact ⟨0, cover_lemma_33⟩
    · exact ⟨4, cover_lemma_34⟩
    · exact ⟨0, cover_lemma_35⟩
    · exact ⟨1, cover_lemma_36⟩
    · exact ⟨0, cover_lemma_37⟩
    · exact ⟨5, cover_lemma_38⟩
    · exact ⟨0, cover_lemma_39⟩
    · exact ⟨1, cover_lemma_40⟩
    · exact ⟨0, cover_lemma_41⟩
    · exact ⟨2, cover_lemma_42⟩
    · exact ⟨0, cover_lemma_43⟩
    · exact ⟨1, cover_lemma_44⟩
    · exact ⟨0, cover_lemma_45⟩
    · exact ⟨3, cover_lemma_46⟩
    · exact ⟨0, cover_lemma_47⟩
    · exact ⟨1, cover_lemma_48⟩
    · exact ⟨0, cover_lemma_49⟩
    · exact ⟨9, cover_lemma_50⟩
    · exact ⟨0, cover_lemma_51⟩
    · exact ⟨1, cover_lemma_52⟩
    · exact ⟨0, cover_lemma_53⟩
    · exact ⟨2, cover_lemma_54⟩
    · exact ⟨0, cover_lemma_55⟩
    · exact ⟨1, cover_lemma_56⟩
    · exact ⟨0, cover_lemma_57⟩
    · exact ⟨4, cover_lemma_58⟩
    · exact ⟨0, cover_lemma_59⟩
    · exact ⟨1, cover_lemma_60⟩
    · exact ⟨0, cover_lemma_61⟩
    · exact ⟨7, cover_lemma_62⟩
    · exact ⟨0, cover_lemma_63⟩
    · exact ⟨1, cover_lemma_64⟩
    · exact ⟨0, cover_lemma_65⟩
    · exact ⟨2, cover_lemma_66⟩
    · exact ⟨0, cover_lemma_67⟩
    · exact ⟨1, cover_lemma_68⟩
    · exact ⟨0, cover_lemma_69⟩
    · exact ⟨4, cover_lemma_70⟩
    · exact ⟨0, cover_lemma_71⟩
    · exact ⟨1, cover_lemma_72⟩
    · exact ⟨0, cover_lemma_73⟩
    · exact ⟨5, cover_lemma_74⟩
    · exact ⟨0, cover_lemma_75⟩
    · exact ⟨1, cover_lemma_76⟩
    · exact ⟨0, cover_lemma_77⟩
    · exact ⟨2, cover_lemma_78⟩
    · exact ⟨0, cover_lemma_79⟩
    · exact ⟨1, cover_lemma_80⟩
    · exact ⟨0, cover_lemma_81⟩
    · exact ⟨4, cover_lemma_82⟩
    · exact ⟨0, cover_lemma_83⟩
    · exact ⟨1, cover_lemma_84⟩
    · exact ⟨0, cover_lemma_85⟩
    · exact ⟨3, cover_lemma_86⟩
    · exact ⟨0, cover_lemma_87⟩
    · exact ⟨1, cover_lemma_88⟩
    · exact ⟨0, cover_lemma_89⟩
    · exact ⟨2, cover_lemma_90⟩
    · exact ⟨0, cover_lemma_91⟩
    · exact ⟨1, cover_lemma_92⟩
    · exact ⟨0, cover_lemma_93⟩
    · exact ⟨4, cover_lemma_94⟩
    · exact ⟨0, cover_lemma_95⟩
    · exact ⟨1, cover_lemma_96⟩
    · exact ⟨0, cover_lemma_97⟩
    · exact ⟨7, cover_lemma_98⟩
    · exact ⟨0, cover_lemma_99⟩
    · exact ⟨1, cover_lemma_100⟩
    · exact ⟨0, cover_lemma_101⟩
    · exact ⟨2, cover_lemma_102⟩
    · exact ⟨0, cover_lemma_103⟩
    · exact ⟨1, cover_lemma_104⟩
    · exact ⟨0, cover_lemma_105⟩
    · exact ⟨3, cover_lemma_106⟩
    · exact ⟨0, cover_lemma_107⟩
    · exact ⟨1, cover_lemma_108⟩
    · exact ⟨0, cover_lemma_109⟩
    · exact ⟨5, cover_lemma_110⟩
    · exact ⟨0, cover_lemma_111⟩
    · exact ⟨1, cover_lemma_112⟩
    · exact ⟨0, cover_lemma_113⟩
    · exact ⟨2, cover_lemma_114⟩
    · exact ⟨0, cover_lemma_115⟩
    · exact ⟨1, cover_lemma_116⟩
    · exact ⟨0, cover_lemma_117⟩
    · exact ⟨4, cover_lemma_118⟩
    · exact ⟨0, cover_lemma_119⟩
    · exact ⟨1, cover_lemma_120⟩
    · exact ⟨0, cover_lemma_121⟩
    · exact ⟨10, cover_lemma_122⟩
    · exact ⟨0, cover_lemma_123⟩
    · exact ⟨1, cover_lemma_124⟩
    · exact ⟨0, cover_lemma_125⟩
    · exact ⟨2, cover_lemma_126⟩
    · exact ⟨0, cover_lemma_127⟩
    · exact ⟨1, cover_lemma_128⟩
    · exact ⟨0, cover_lemma_129⟩
    · exact ⟨4, cover_lemma_130⟩
    · exact ⟨0, cover_lemma_131⟩
    · exact ⟨1, cover_lemma_132⟩
    · exact ⟨0, cover_lemma_133⟩
    · exact ⟨6, cover_lemma_134⟩
    · exact ⟨0, cover_lemma_135⟩
    · exact ⟨1, cover_lemma_136⟩
    · exact ⟨0, cover_lemma_137⟩
    · exact ⟨2, cover_lemma_138⟩
    · exact ⟨0, cover_lemma_139⟩
    · exact ⟨1, cover_lemma_140⟩
    · exact ⟨0, cover_lemma_141⟩
    · exact ⟨4, cover_lemma_142⟩
    · exact ⟨0, cover_lemma_143⟩
    · exact ⟨1, cover_lemma_144⟩
    · exact ⟨0, cover_lemma_145⟩
    · exact ⟨3, cover_lemma_146⟩
    · exact ⟨0, cover_lemma_147⟩
    · exact ⟨1, cover_lemma_148⟩
    · exact ⟨0, cover_lemma_149⟩
    · exact ⟨2, cover_lemma_150⟩
    · exact ⟨0, cover_lemma_151⟩
    · exact ⟨1, cover_lemma_152⟩
    · exact ⟨0, cover_lemma_153⟩
    · exact ⟨4, cover_lemma_154⟩
    · exact ⟨0, cover_lemma_155⟩
    · exact ⟨1, cover_lemma_156⟩
    · exact ⟨0, cover_lemma_157⟩
    · exact ⟨8, cover_lemma_158⟩
    · exact ⟨0, cover_lemma_159⟩
    · exact ⟨1, cover_lemma_160⟩
    · exact ⟨0, cover_lemma_161⟩
    · exact ⟨2, cover_lemma_162⟩
    · exact ⟨0, cover_lemma_163⟩
    · exact ⟨1, cover_lemma_164⟩
    · exact ⟨0, cover_lemma_165⟩
    · exact ⟨3, cover_lemma_166⟩
    · exact ⟨0, cover_lemma_167⟩
    · exact ⟨1, cover_lemma_168⟩
    · exact ⟨0, cover_lemma_169⟩
    · exact ⟨7, cover_lemma_170⟩
    · exact ⟨0, cover_lemma_171⟩
    · exact ⟨1, cover_lemma_172⟩
    · exact ⟨0, cover_lemma_173⟩
    · exact ⟨2, cover_lemma_174⟩
    · exact ⟨0, cover_lemma_175⟩
    · exact ⟨1, cover_lemma_176⟩
    · exact ⟨0, cover_lemma_177⟩
    · exact ⟨4, cover_lemma_178⟩
    · exact ⟨0, cover_lemma_179⟩
    · exact ⟨1, cover_lemma_180⟩
    · exact ⟨0, cover_lemma_181⟩
    · exact ⟨5, cover_lemma_182⟩
    · exact ⟨0, cover_lemma_183⟩
    · exact ⟨1, cover_lemma_184⟩
    · exact ⟨0, cover_lemma_185⟩
    · exact ⟨2, cover_lemma_186⟩
    · exact ⟨0, cover_lemma_187⟩
    · exact ⟨1, cover_lemma_188⟩
    · exact ⟨0, cover_lemma_189⟩
    · exact ⟨4, cover_lemma_190⟩
    · exact ⟨0, cover_lemma_191⟩
    · exact ⟨1, cover_lemma_192⟩
    · exact ⟨0, cover_lemma_193⟩
    · exact ⟨6, cover_lemma_194⟩
    · exact ⟨0, cover_lemma_195⟩
    · exact ⟨1, cover_lemma_196⟩
    · exact ⟨0, cover_lemma_197⟩
    · exact ⟨2, cover_lemma_198⟩
    · exact ⟨0, cover_lemma_199⟩
    · exact ⟨1, cover_lemma_200⟩
    · exact ⟨0, cover_lemma_201⟩
    · exact ⟨4, cover_lemma_202⟩
    · exact ⟨0, cover_lemma_203⟩
    · exact ⟨1, cover_lemma_204⟩
    · exact ⟨0, cover_lemma_205⟩
    · exact ⟨3, cover_lemma_206⟩
    · exact ⟨0, cover_lemma_207⟩
    · exact ⟨1, cover_lemma_208⟩
    · exact ⟨0, cover_lemma_209⟩
    · exact ⟨2, cover_lemma_210⟩
    · exact ⟨0, cover_lemma_211⟩
    · exact ⟨1, cover_lemma_212⟩
    · exact ⟨0, cover_lemma_213⟩
    · exact ⟨4, cover_lemma_214⟩
    · exact ⟨0, cover_lemma_215⟩
    · exact ⟨1, cover_lemma_216⟩
    · exact ⟨0, cover_lemma_217⟩
    · exact ⟨5, cover_lemma_218⟩
    · exact ⟨0, cover_lemma_219⟩
    · exact ⟨1, cover_lemma_220⟩
    · exact ⟨0, cover_lemma_221⟩
    · exact ⟨2, cover_lemma_222⟩
    · exact ⟨0, cover_lemma_223⟩
    · exact ⟨1, cover_lemma_224⟩
    · exact ⟨0, cover_lemma_225⟩
    · exact ⟨3, cover_lemma_226⟩
    · exact ⟨0, cover_lemma_227⟩
    · exact ⟨1, cover_lemma_228⟩
    · exact ⟨0, cover_lemma_229⟩
    · exact ⟨9, cover_lemma_230⟩
    · exact ⟨0, cover_lemma_231⟩
    · exact ⟨1, cover_lemma_232⟩
    · exact ⟨0, cover_lemma_233⟩
    · exact ⟨2, cover_lemma_234⟩
    · exact ⟨0, cover_lemma_235⟩
    · exact ⟨1, cover_lemma_236⟩
    · exact ⟨0, cover_lemma_237⟩
    · exact ⟨4, cover_lemma_238⟩
    · exact ⟨0, cover_lemma_239⟩
    · exact ⟨1, cover_lemma_240⟩
    · exact ⟨0, cover_lemma_241⟩
    · exact ⟨7, cover_lemma_242⟩
    · exact ⟨0, cover_lemma_243⟩
    · exact ⟨1, cover_lemma_244⟩
    · exact ⟨0, cover_lemma_245⟩
    · exact ⟨2, cover_lemma_246⟩
    · exact ⟨0, cover_lemma_247⟩
    · exact ⟨1, cover_lemma_248⟩
    · exact ⟨0, cover_lemma_249⟩
    · exact ⟨4, cover_lemma_250⟩
    · exact ⟨0, cover_lemma_251⟩
    · exact ⟨1, cover_lemma_252⟩
    · exact ⟨0, cover_lemma_253⟩
    · exact ⟨5, cover_lemma_254⟩
    · exact ⟨0, cover_lemma_255⟩
    · exact ⟨1, cover_lemma_256⟩
    · exact ⟨0, cover_lemma_257⟩
    · exact ⟨2, cover_lemma_258⟩
    · exact ⟨0, cover_lemma_259⟩
    · exact ⟨1, cover_lemma_260⟩
    · exact ⟨0, cover_lemma_261⟩
    · exact ⟨4, cover_lemma_262⟩
    · exact ⟨0, cover_lemma_263⟩
    · exact ⟨1, cover_lemma_264⟩
    · exact ⟨0, cover_lemma_265⟩
    · exact ⟨3, cover_lemma_266⟩
    · exact ⟨0, cover_lemma_267⟩
    · exact ⟨1, cover_lemma_268⟩
    · exact ⟨0, cover_lemma_269⟩
    · exact ⟨2, cover_lemma_270⟩
    · exact ⟨0, cover_lemma_271⟩
    · exact ⟨1, cover_lemma_272⟩
    · exact ⟨0, cover_lemma_273⟩
    · exact ⟨4, cover_lemma_274⟩
    · exact ⟨0, cover_lemma_275⟩
    · exact ⟨1, cover_lemma_276⟩
    · exact ⟨0, cover_lemma_277⟩
    · exact ⟨7, cover_lemma_278⟩
    · exact ⟨0, cover_lemma_279⟩
    · exact ⟨1, cover_lemma_280⟩
    · exact ⟨0, cover_lemma_281⟩
    · exact ⟨2, cover_lemma_282⟩
    · exact ⟨0, cover_lemma_283⟩
    · exact ⟨1, cover_lemma_284⟩
    · exact ⟨0, cover_lemma_285⟩
    · exact ⟨3, cover_lemma_286⟩
    · exact ⟨0, cover_lemma_287⟩
    · exact ⟨1, cover_lemma_288⟩
    · exact ⟨0, cover_lemma_289⟩
    · exact ⟨5, cover_lemma_290⟩
    · exact ⟨0, cover_lemma_291⟩
    · exact ⟨1, cover_lemma_292⟩
    · exact ⟨0, cover_lemma_293⟩
    · exact ⟨2, cover_lemma_294⟩
    · exact ⟨0, cover_lemma_295⟩
    · exact ⟨1, cover_lemma_296⟩
    · exact ⟨0, cover_lemma_297⟩
    · exact ⟨4, cover_lemma_298⟩
    · exact ⟨0, cover_lemma_299⟩
    · exact ⟨1, cover_lemma_300⟩
    · exact ⟨0, cover_lemma_301⟩
    · exact ⟨11, cover_lemma_302⟩
    · exact ⟨0, cover_lemma_303⟩
    · exact ⟨1, cover_lemma_304⟩
    · exact ⟨0, cover_lemma_305⟩
    · exact ⟨2, cover_lemma_306⟩
    · exact ⟨0, cover_lemma_307⟩
    · exact ⟨1, cover_lemma_308⟩
    · exact ⟨0, cover_lemma_309⟩
    · exact ⟨4, cover_lemma_310⟩
    · exact ⟨0, cover_lemma_311⟩
    · exact ⟨1, cover_lemma_312⟩
    · exact ⟨0, cover_lemma_313⟩
    · exact ⟨6, cover_lemma_314⟩
    · exact ⟨0, cover_lemma_315⟩
    · exact ⟨1, cover_lemma_316⟩
    · exact ⟨0, cover_lemma_317⟩
    · exact ⟨2, cover_lemma_318⟩
    · exact ⟨0, cover_lemma_319⟩
    · exact ⟨1, cover_lemma_320⟩
    · exact ⟨0, cover_lemma_321⟩
    · exact ⟨4, cover_lemma_322⟩
    · exact ⟨0, cover_lemma_323⟩
    · exact ⟨1, cover_lemma_324⟩
    · exact ⟨0, cover_lemma_325⟩
    · exact ⟨3, cover_lemma_326⟩
    · exact ⟨0, cover_lemma_327⟩
    · exact ⟨1, cover_lemma_328⟩
    · exact ⟨0, cover_lemma_329⟩
    · exact ⟨2, cover_lemma_330⟩
    · exact ⟨0, cover_lemma_331⟩
    · exact ⟨1, cover_lemma_332⟩
    · exact ⟨0, cover_lemma_333⟩
    · exact ⟨4, cover_lemma_334⟩
    · exact ⟨0, cover_lemma_335⟩
    · exact ⟨1, cover_lemma_336⟩
    · exact ⟨0, cover_lemma_337⟩
    · exact ⟨10, cover_lemma_338⟩
    · exact ⟨0, cover_lemma_339⟩
    · exact ⟨1, cover_lemma_340⟩
    · exact ⟨0, cover_lemma_341⟩
    · exact ⟨2, cover_lemma_342⟩
    · exact ⟨0, cover_lemma_343⟩
    · exact ⟨1, cover_lemma_344⟩
    · exact ⟨0, cover_lemma_345⟩
    · exact ⟨3, cover_lemma_346⟩
    · exact ⟨0, cover_lemma_347⟩
    · exact ⟨1, cover_lemma_348⟩
    · exact ⟨0, cover_lemma_349⟩
    · exact ⟨7, cover_lemma_350⟩
    · exact ⟨0, cover_lemma_351⟩
    · exact ⟨1, cover_lemma_352⟩
    · exact ⟨0, cover_lemma_353⟩
    · exact ⟨2, cover_lemma_354⟩
    · exact ⟨0, cover_lemma_355⟩
    · exact ⟨1, cover_lemma_356⟩
    · exact ⟨0, cover_lemma_357⟩
    · exact ⟨4, cover_lemma_358⟩
    · exact ⟨0, cover_lemma_359⟩

  rcases h_cases with ⟨i, hi⟩
  use i
  have h_div := mods_dvd_360 i
  have h_eq : x % mods i = (x % 360) % mods i := by
    rw [Nat.mod_mod_of_dvd x h_div]
  rw [h_eq]
  exact hi

lemma mem_coset_of_mod (x : ℕ) (i : Fin 12) (h : x % mods i = rems i) :
    x ∈ ({rems i} : Set ℕ) + (Ideal.span {mods i} : Set ℕ) := by
  simp only [Set.mem_add, Set.mem_singleton_iff]
  have h1 : rems i ≤ x % mods i := by rw [h]
  have h2 : x % mods i ≤ x := Nat.mod_le x _
  have h3 : rems i ≤ x := le_trans h1 h2
  refine ⟨rems i, rfl, x - rems i, ?_, ?_⟩
  · change x - rems i ∈ Ideal.span {mods i}
    rw [Ideal.mem_span_singleton]
    use x / mods i
    have h_eq : x = mods i * (x / mods i) + x % mods i := (Nat.div_add_mod x (mods i)).symm
    rw [h] at h_eq
    omega
  · rw [Nat.add_sub_cancel' h3]

def sys : StrictCoveringSystem ℕ where
  ι := Fin 12
  residue := rems
  moduli i := Ideal.span {mods i}
  unionCovers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases covers_360 x with ⟨i, hi⟩
    use i
    exact mem_coset_of_mod x i hi
  non_trivial := mods_not_bot
  injective_moduli := by
    intro i j hij
    change Ideal.span {mods i} = Ideal.span {mods j} at hij
    have hi : mods i ∈ Ideal.span {mods j} := by
      rw [←hij]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hj : mods j ∈ Ideal.span {mods i} := by
      rw [hij]
      exact Ideal.subset_span (Set.mem_singleton _)
    change mods i ∈ Ideal.span {mods j} at hi
    change mods j ∈ Ideal.span {mods i} at hj
    rw [Ideal.mem_span_singleton] at hi hj
    have hdvd1 : mods j ∣ mods i := hi
    have hdvd2 : mods i ∣ mods j := hj
    have heq : mods i = mods j := Nat.dvd_antisymm hdvd2 hdvd1
    exact mods_inj heq

@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/YOUR_PR_NUMBER", AMS 5 11]
theorem erdos_273.variants.three : answer(True) ↔ ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} := by
  have H : ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} := by
    use sys
    intro i
    use primes i
    have hp := primes_valid i
    rcases hp with ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, hp2, ?_⟩
    dsimp [sys]
    rw [hp3]
  exact ⟨fun _ => H, fun _ => trivial⟩

end Erdos273

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

import Mathlib.Computability.PostTuringMachine
import Mathlib.Logic.Relation

open Turing

lemma dom_of_apply_eq_none  {σ : Type*} {f : σ → Option σ} {s : σ} (hf : f s = none) :
    s ∈ Turing.eval f s := by
  apply PFun.fix_stop
  simp [hf]

@[simp]
theorem Turing.apply_get_eval {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom) :
    f ((Turing.eval f s).get H) = none := by
  have := Part.get_mem H
  rw [mem_eval] at this
  exact this.right

theorem Part.get_eq_get {σ : Type*} {a b : Part σ} (ha : a.Dom) (hb : a.get ha ∈ b) : a = b := by
  have hb' : b.Dom := by
    rw [Part.dom_iff_mem]
    use a.get ha
  rw [← Part.eq_get_iff_mem hb'] at hb
  ext c
  rw [← Part.eq_get_iff_mem ha, ← Part.eq_get_iff_mem hb', hb]

-- TODO(Paul-Lez): also prove this for `PFun.fix`/golf using the `PFun.fix` API
theorem Turing.eval_get_eval {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom) :
    Turing.eval f ((Turing.eval f s).get H) = Turing.eval f s := by
  symm
  apply Part.get_eq_get H (dom_of_apply_eq_none ?_)
  simp

-- TODO(Paul-Lez): also prove this for `PFun.fix`/golf using the `PFun.fix` API
theorem Turing.eval_eq_eval {σ : Type*} {f : σ → Option σ} {a a' : σ} (H : f a = some a'):
    Turing.eval f a = Turing.eval f a' := by
  apply reaches_eval
  rw [Turing.Reaches]
  apply Relation.ReflTransGen.single
  rw [H]
  rfl

-- TODO(lezeau): this should be generalized to `PFun.fix`
theorem eval_dom_iff {σ : Type*} {f : σ → Option σ} {s : σ} :
    (∃ n, ((Option.bind · f)^[n+1] s) = none) ↔ (Turing.eval f s).Dom := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · obtain ⟨n, hn⟩ := H
    induction n generalizing s with
    | zero =>
      rw [zero_add, Function.iterate_one, Option.some_bind] at hn
      simpa [Part.dom_iff_mem] using ⟨s, dom_of_apply_eq_none hn⟩
    | succ n ih =>
      obtain ha | ⟨a', ha'⟩ := (f s).eq_none_or_eq_some
      · simpa [Part.dom_iff_mem] using ⟨s, dom_of_apply_eq_none ha⟩
      · simp_rw [Function.iterate_succ, Function.comp_apply, Option.some_bind] at hn ih
        simp_rw [ha', Option.some_bind] at hn
        have ih := @ih a' hn
        rwa [Turing.eval_eq_eval ha']
  · set C : σ → Prop := fun s ↦ (Turing.eval f s).Dom → ∃ n, (Option.bind · f)^[n+1] s = none
    apply evalInduction (C := C) (a := s) (h := Part.get_mem H) _ H
    intro a ha h HH
    obtain ha | ⟨a', ha'⟩ := (f a).eq_none_or_eq_some
    · use 0
      simp [ha]
    · obtain ⟨n, hn⟩ := h a' ha' (by rwa [←Turing.eval_eq_eval ha'])
      use n + 1
      simp only [Function.iterate_succ, Function.comp_apply, Option.some_bind] at hn
      simp [ha', hn]

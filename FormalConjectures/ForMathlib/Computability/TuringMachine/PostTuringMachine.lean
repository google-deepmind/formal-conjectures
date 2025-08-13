import Mathlib.Computability.PostTuringMachine
import Mathlib.Logic.Relation

open Turing

lemma Option.bind_iterate {α} (f : α → Option α) (a : Option α) (n : ℕ)  :
    (Option.bind · f)^[n+1] a = Option.bind ((Option.bind · f)^[n] a) f := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ', Function.comp_apply, ih]

lemma Option.bind_iterate' {α} (f : α → Option α) (a : Option α) (n : ℕ)  :
    (Option.bind · f)^[n+1] a = (Option.bind · f)^[n] (a.bind f) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ, Function.comp_apply, ih]

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

theorem dom_eval_of_dom {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom) :
    (Turing.eval f ((Turing.eval f s).get H)).Dom := by
  suffices Turing.eval f ((Turing.eval f s).get H) = Turing.eval f s by rwa [this]
  have : (Turing.eval f s).get H ∈ Turing.eval f ((Turing.eval f s).get H) := by
    apply dom_of_apply_eq_none
    simp
  symm
  apply Part.get_eq_get H this

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
      · simp_rw [Option.bind_iterate', Option.some_bind] at hn ih
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
      simp [Option.bind_iterate', Option.some_bind, ha', Option.bind_iterate', Option.some_bind, hn]

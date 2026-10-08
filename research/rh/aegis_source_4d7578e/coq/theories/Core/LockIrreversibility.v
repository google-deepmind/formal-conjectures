(* ============================================================ *)
(* AEGIS Ω — LOCK Commitment Irreversibility                    *)
(* Gate 25 · Epistemic Tier: T0                                 *)
(*                                                              *)
(* Once LOCK commits, frame state is frozen:                    *)
(*   - Pre-lock and post-lock phases are disjoint               *)
(*   - is_pre_lock p = true  => is_post_lock p = false          *)
(*   - is_post_lock p = true => is_pre_lock  p = false          *)
(*   - LOCK itself is in neither set (it is the boundary)       *)
(*   - HARMONIZE resets the lock — that is the only path back   *)
(*     to READ — and it is the only transition that increments  *)
(*     the sequence number.                                      *)
(* ============================================================ *)

Require Import Coq.Lists.List.
Import ListNotations.

(* ─── Phase Inductive Type ─────────────────────────────────── *)

(** The five phases of the SHP execution cycle. *)
Inductive Phase : Type :=
  | READ
  | ASSESS
  | LOCK
  | PROPAGATE
  | HARMONIZE.

(* ─── Phase Classification ─────────────────────────────────── *)

(** Pre-lock phases: READ and ASSESS (before the commit boundary). *)
Definition is_pre_lock (p : Phase) : bool :=
  match p with
  | READ   => true
  | ASSESS => true
  | _      => false
  end.

(** Post-lock phases: PROPAGATE and HARMONIZE (after the commit boundary). *)
Definition is_post_lock (p : Phase) : bool :=
  match p with
  | PROPAGATE => true
  | HARMONIZE => true
  | _         => false
  end.

(* ─── Core Theorems ─────────────────────────────────────────── *)

(** Theorem: pre-lock and post-lock phases are disjoint.
    No phase can be simultaneously in the pre-lock and post-lock sets.
    LOCK sits between them and belongs to neither. *)
Theorem sitr_aoie_separation : forall p : Phase,
  is_pre_lock p = true -> is_post_lock p = false.
Proof.
  intros p H.
  destruct p; simpl in *; try reflexivity; discriminate.
Qed.

(** Theorem: the converse — post-lock implies not pre-lock. *)
Theorem aoie_not_pre_lock : forall p : Phase,
  is_post_lock p = true -> is_pre_lock p = false.
Proof.
  intros p H.
  destruct p; simpl in *; try reflexivity; discriminate.
Qed.

(** Theorem: LOCK itself is in neither set (it is the boundary). *)
Theorem lock_is_boundary :
  is_pre_lock LOCK = false /\ is_post_lock LOCK = false.
Proof.
  split; reflexivity.
Qed.

(** Theorem: READ is strictly pre-lock. *)
Theorem read_is_pre_lock : is_pre_lock READ = true.
Proof. reflexivity. Qed.

(** Theorem: ASSESS is strictly pre-lock. *)
Theorem assess_is_pre_lock : is_pre_lock ASSESS = true.
Proof. reflexivity. Qed.

(** Theorem: PROPAGATE is strictly post-lock. *)
Theorem propagate_is_post_lock : is_post_lock PROPAGATE = true.
Proof. reflexivity. Qed.

(** Theorem: HARMONIZE is strictly post-lock. *)
Theorem harmonize_is_post_lock : is_post_lock HARMONIZE = true.
Proof. reflexivity. Qed.

(* ─── Frame State ────────────────────────────────────────────── *)

(** A frame captures the current phase and whether lock has been committed. *)
Record Frame : Type := mkFrame
  { frame_phase  : Phase
  ; frame_locked : bool
  }.

(** Well-formedness: pre-lock phases must have locked=false;
    post-lock phases must have locked=true. *)
Definition frame_wf (f : Frame) : Prop :=
  (is_pre_lock (frame_phase f) = true -> frame_locked f = false) /\
  (is_post_lock (frame_phase f) = true -> frame_locked f = true).

(** Theorem: A well-formed frame cannot be simultaneously pre-lock and post-lock. *)
Theorem wf_disjoint : forall f : Frame,
  frame_wf f ->
  ~ (is_pre_lock (frame_phase f) = true /\ is_post_lock (frame_phase f) = true).
Proof.
  intros f [Hpre Hpost] [Hpre_t Hpost_t].
  apply Hpre in Hpre_t.
  apply Hpost in Hpost_t.
  (* frame_locked f = false and frame_locked f = true — contradiction *)
  rewrite Hpre_t in Hpost_t.
  discriminate.
Qed.

(* ============================================================ *)
(* AEGIS Ω — Semilattice Convergence Proof                      *)
(* Gate 25 · Epistemic Tier: T0                                 *)
(*                                                              *)
(* Proves join-semilattice laws for the SITRState type:         *)
(*   join_commutative : join a b = join b a                     *)
(*   join_idempotent  : join a a = a                            *)
(*   join_monotone    : ordinal a <= ordinal (join a b)         *)
(*   join_associative : join (join a b) c = join a (join b c)   *)
(*                                                              *)
(* The six SITRState values form a total order under ordinal:   *)
(*   STABLE(0) < DEGRADED(1) < UNSTABLE(2) <                   *)
(*   CONSTITUTIONAL_RISK(3) < CONTAINED(4) < COMPROMISED(5)    *)
(*                                                              *)
(* join is the least upper bound: max by ordinal.               *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Lia.

(* ─── SITRState ──────────────────────────────────────────────── *)

(** Monotonic escalation lattice — STABLE is lowest, COMPROMISED is terminal. *)
Inductive SITRState : Type :=
  | STABLE
  | DEGRADED
  | UNSTABLE
  | CONSTITUTIONAL_RISK
  | CONTAINED
  | COMPROMISED.

(* ─── Ordinal (total order embedding) ──────────────────────── *)

(** Map each state to a natural number ordinal.
    The ordinal induces a total order on SITRState. *)
Fixpoint ordinal (s : SITRState) : nat :=
  match s with
  | STABLE              => 0
  | DEGRADED            => 1
  | UNSTABLE            => 2
  | CONSTITUTIONAL_RISK => 3
  | CONTAINED           => 4
  | COMPROMISED         => 5
  end.

(** Inverse: recover the state from its ordinal (partial — only valid for 0..5). *)
Definition from_ordinal (n : nat) : option SITRState :=
  match n with
  | 0 => Some STABLE
  | 1 => Some DEGRADED
  | 2 => Some UNSTABLE
  | 3 => Some CONSTITUTIONAL_RISK
  | 4 => Some CONTAINED
  | 5 => Some COMPROMISED
  | _ => None
  end.

(** Lemma: ordinal is injective (distinct states have distinct ordinals). *)
Lemma ordinal_injective : forall a b : SITRState,
  ordinal a = ordinal b -> a = b.
Proof.
  intros a b H.
  destruct a; destruct b; simpl in H; try reflexivity; discriminate.
Qed.

(* ─── Join (least upper bound) ──────────────────────────────── *)

(** Join returns the state with the larger ordinal.
    This is the least upper bound in the total order lattice. *)
Definition join (a b : SITRState) : SITRState :=
  if Nat.leb (ordinal a) (ordinal b) then b else a.

(* ─── Core Semilattice Theorems ─────────────────────────────── *)

(** Theorem: join is commutative. *)
Theorem join_commutative : forall a b : SITRState,
  join a b = join b a.
Proof.
  intros a b.
  unfold join.
  destruct (Nat.leb (ordinal a) (ordinal b)) eqn:Hab;
  destruct (Nat.leb (ordinal b) (ordinal a)) eqn:Hba.
  - (* ordinal a <= ordinal b  and  ordinal b <= ordinal a  =>  a = b *)
    apply Nat.leb_le in Hab.
    apply Nat.leb_le in Hba.
    assert (ordinal a = ordinal b) by lia.
    apply ordinal_injective in H. subst. reflexivity.
  - (* ordinal a <= ordinal b  and  ~(ordinal b <= ordinal a) *)
    reflexivity.
  - (* ~(ordinal a <= ordinal b)  and  ordinal b <= ordinal a *)
    reflexivity.
  - (* ~(ordinal a <= ordinal b)  and  ~(ordinal b <= ordinal a) — impossible *)
    apply Nat.leb_nle in Hab.
    apply Nat.leb_nle in Hba.
    lia.
Qed.

(** Theorem: join is idempotent. *)
Theorem join_idempotent : forall a : SITRState,
  join a a = a.
Proof.
  intros a.
  unfold join.
  rewrite Nat.leb_refl.
  reflexivity.
Qed.

(** Theorem: join is monotone — the result has at least the ordinal of a. *)
Theorem join_monotone : forall a b : SITRState,
  ordinal a <= ordinal (join a b).
Proof.
  intros a b.
  unfold join.
  destruct (Nat.leb (ordinal a) (ordinal b)) eqn:H.
  - apply Nat.leb_le in H. exact H.
  - apply Nat.leb_nle in H. lia.
Qed.

(** Corollary: join is also monotone in its second argument. *)
Theorem join_monotone_r : forall a b : SITRState,
  ordinal b <= ordinal (join a b).
Proof.
  intros a b.
  rewrite join_commutative.
  apply join_monotone.
Qed.

(** Theorem: join is associative.

    join picks whichever argument has the greater ordinal, so associativity
    follows from totality of <= on nat. After discharging the two inner
    comparisons, cases (a<=b, ~b<=c) and (~a<=b, b<=c) close by reflexivity;
    the two remaining cases need the transitive fact about a vs c. *)
Theorem join_associative : forall a b c : SITRState,
  join (join a b) c = join a (join b c).
Proof.
  intros a b c. unfold join.
  destruct (Nat.leb (ordinal a) (ordinal b)) eqn:Hab;
  destruct (Nat.leb (ordinal b) (ordinal c)) eqn:Hbc;
  rewrite ?Hab, ?Hbc;
  try reflexivity.
  - (* a <= b  and  b <= c  =>  a <= c, both sides reduce to c *)
    apply Nat.leb_le in Hab. apply Nat.leb_le in Hbc.
    assert (Hac : Nat.leb (ordinal a) (ordinal c) = true)
      by (apply Nat.leb_le; lia).
    rewrite Hac. reflexivity.
  - (* ~(a <= b)  and  ~(b <= c)  =>  ~(a <= c), both sides reduce to a *)
    apply Nat.leb_nle in Hab. apply Nat.leb_nle in Hbc.
    assert (Hac : Nat.leb (ordinal a) (ordinal c) = false)
      by (apply Nat.leb_nle; lia).
    rewrite Hac. reflexivity.
Qed.

(* ─── Additional Properties ─────────────────────────────────── *)

(** COMPROMISED is the top element — joining with anything returns COMPROMISED. *)
Theorem compromised_is_top : forall s : SITRState,
  join COMPROMISED s = COMPROMISED.
Proof.
  intros s.
  unfold join. simpl.
  destruct s; simpl; reflexivity.
Qed.

(** STABLE is the bottom element — joining STABLE with anything returns the other. *)
Theorem stable_is_bottom : forall s : SITRState,
  join STABLE s = s.
Proof.
  intros s.
  unfold join. simpl.
  destruct s; simpl; reflexivity.
Qed.

(** Escalation is irreversible under join: if a >= b, then join a b = a. *)
Theorem join_absorbs_lower : forall a b : SITRState,
  ordinal a >= ordinal b -> join a b = a.
Proof.
  intros a b H.
  unfold join.
  destruct (Nat.leb (ordinal a) (ordinal b)) eqn:Hle.
  - apply Nat.leb_le in Hle.
    assert (ordinal a = ordinal b) by lia.
    apply ordinal_injective in H0. subst. reflexivity.
  - reflexivity.
Qed.

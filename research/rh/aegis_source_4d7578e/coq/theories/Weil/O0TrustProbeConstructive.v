(*
  AEGIS Ω — O₀ constructive-real trust probe

  Diagnostic only. This file asks whether the Coq 8.20 constructive Cauchy-real
  implementation can carry the order relation needed by the O₀ globalization
  layer while remaining Closed under the global context.

  It is not production O₀ mathematics and it proves nothing about Weil or RH.
*)

From Coq Require Import Reals.Abstract.ConstructiveReals.
From Coq Require Import Reals.Cauchy.ConstructiveRcomplete.

Definition O0ConstructiveRealV1 : Type :=
  CRcarrier CRealConstructive.

Theorem o0_trust_probe_constructive_order_refl :
  forall x : O0ConstructiveRealV1,
    CRle CRealConstructive x x.
Proof.
  intros x.
  apply CRle_refl.
Qed.

(* AEGIS Ω O₀ closure probe.
   Expected slice-1 state: O0 imports, but O0_closure does not exist. *)

Require Import O0.

Fail Check O0_closure.
Check o0_status.

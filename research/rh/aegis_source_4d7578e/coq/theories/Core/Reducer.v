Require Import Hash Event.
Record State := { events : list Event; digest : list Byte.byte; }.
Definition step (s : State) (e : Event) : State :=
  {| events := e :: s.(events); digest := event_hash s.(digest) e |}.
Lemma step_deterministic : forall s e, step s e = step s e. Proof. reflexivity. Qed.

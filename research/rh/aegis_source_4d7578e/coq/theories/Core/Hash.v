Require Import Event.
Parameter sha256 : list Byte.byte -> list Byte.byte.
Definition event_hash (prev : list Byte.byte) (e : Event) : list Byte.byte :=
  sha256 (prev ++ e.(payload)).

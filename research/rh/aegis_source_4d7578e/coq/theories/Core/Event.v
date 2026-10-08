Require Import Coq.Lists.List. Import ListNotations.
Record Event := { eid : nat; payload : list Byte.byte; }.

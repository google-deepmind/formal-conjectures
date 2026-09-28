/-
Copyright 2026 The Formal Conjectures Authors.

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
module

public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-!
# `Primcodable` instances from retractions

`Primcodable.ofLeftInverse` builds a `Primcodable` instance on a type `β` from a map `f : β → α`
into a `Primcodable` type `α` together with a left inverse `finv` of `f` such that `f ∘ finv` is
primitive recursive. This is the `Primcodable` analogue of `Encodable.ofLeftInverse`, and applies
in particular to sigma types, for which Mathlib provides no `Primcodable` instance.
-/

namespace Primcodable

variable {α β : Type*} [Primcodable α]

/-- If `f : β → α` has a left inverse `finv` such that `f ∘ finv` is primitive recursive, then `β`
is `Primcodable`, with `b` encoded as `Encodable.encode (f b)`. -/
@[instance_reducible]
def ofLeftInverse (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b)
    (hf : Primrec fun a => f (finv a)) : Primcodable β :=
  letI : Encodable β := Encodable.ofLeftInverse f finv linv
  { prim := Primrec.nat_iff.1 <| (Primrec.encode.comp
      (Primrec.option_map Primrec.decode (hf.comp₂ Primrec₂.right))).of_eq fun n => by
        have key : ∀ o : Option α, Encodable.encode (o.map fun a => f (finv a)) =
            Encodable.encode (α := Option β) (o.bind (some ∘ finv)) := fun o => by cases o <;> rfl
        exact key _ }

end Primcodable

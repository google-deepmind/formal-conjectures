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
import FormalConjecturesUtil

/-!
# Tao's Optimization Constant 14 / Smallest $n$ for which the value of $BB(n)$ is undecidable

*References:*
- [Tao's Optimization Constant 14](https://teorth.github.io/optimizationproblems/constants/14a.html)
- [LS1965] Lin, S. and Radó, T., [*Computer studies of Turing machine
  problems*](https://doi.org/10.1145/321264.321270). J. ACM **12** (1965), 196–212.
- [B1983] Brady, A. H., [*The determination of Radó's noncomputable function $\Sigma(k)$ for
  four-state Turing machines*](https://docs.bbchallenge.org/papers/Brady1983.pdf).
  Math. Comp. **40** (1983), 647–665.
- [BB2025] Blanchard, J. et al., *Determination of the fifth Busy Beaver value* (2025).
  [arXiv:2509.12337](https://arxiv.org/abs/2509.12337)
- [YS2016] Yedidia, A. and Aaronson, S., *A relatively small Turing machine whose behavior is
  independent of set theory* (2016). [arXiv:1605.04343](https://arxiv.org/abs/1605.04343)
- [O2016] O'Rear, S.,
  [*metamath-turing-machines*](https://github.com/sorear/metamath-turing-machines) (2016).
- [W2025] Wade, A. J.,
  [*turing_machine_explorer*](https://codeberg.org/ajwade/turing_machine_explorer) (2025).
- [A2020] Aaronson, S., [*The Busy Beaver
  Frontier*](https://doi.org/10.1145/3427361.3427369). ACM SIGACT News **51** (2020), 32–54.

This file defines the smallest $n$ for which the value of $BB(n)$ is undecidable. More precisely,
it formalizes the least number of states for which ZFC can neither prove nor disprove that a
specific Turing machine halts. Its existence and known upper bounds follow from Gödel's second
incompleteness theorem.

We do this by modeling a version of first order logic, ZFC and Turing machines within Lean.
The implementation of FOL and ZFC is taken from the
[FormalizedLogicLean](https://github.com/FormalizedFormalLogic/Foundation) project.
The implementation is copied and minimized from that project. It is not necessary to read it to
understand the definition of `C14`. The copied definitions span the section
`FormalizedFormalLogic`. Confidence in that implementation partly comes from the large body of
proofs developed with it, including formalizations of independence theorems.

This is followed by a model of Turing machines within the first-order logic framework, developed
for Formal Conjectures in the section `BackgroundDefs`. The file then defines `C14` and states its
known bounds and related conjectures. The known bounds use `sorry`; formalizing one would be a
substantial achievement.

-/

universe u v₁ v₂ v

section FormalizedFormalLogic

section

namespace Multiset

variable {α : Type*}

/-- Function to avoid reducing `{a} + s` to `a ::ₘ s` -/
def atom (a : α) : Multiset α := {a}

/-- `⦃x, y, z, ...⦄` notation for `kpair` -/
syntax "⦃" term,* "⦄" : term

macro_rules
  | `(⦃$terms:term,*, $term:term⦄) => `(⦃$terms,*⦄ + atom $term)
  | `(⦃$term:term⦄) => `(atom $term)
  | `(⦃⦄) => `(0)

end Multiset

end

section

namespace Nat

variable {α : ℕ → Sort u}

def cases (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : ∀ n, α n
  | 0     => hzero
  | n + 1 => hsucc n

infixr:70 " :>ₙ " => cases

end Nat

end

section

namespace Fin

variable {n : ℕ} (m : ℕ)

@[inline] def addCast (m) : Fin n → Fin (m + n) := castLE <| Nat.le_add_left n m

end Fin

end

section

namespace Matrix

section

variable {n : ℕ} {α : Type u}

infixr:70 " :> " => vecCons

def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

infixl:70 " <: " => vecConsLast

end

end Matrix

end

section

namespace FFL

class HTilde (α : Type*) (β : outParam Type*) where
  hTilde : α → β

prefix:75 "∼" => HTilde.hTilde

macro_rules | `(∼$x) => `(unop% HTilde.hTilde $x)

class HArrow (α β : Type*) (γ : outParam Type*) where
  hArrow : α → β → γ

infixr:60 " 🡒 " => HArrow.hArrow

macro_rules | `($x 🡒 $y) => `(binop% HArrow.hArrow $x $y)

class HWedge (α β : Type*) (γ : outParam Type*) where
  hWedge : α → β → γ

infixr:69 " ⋏ " => HWedge.hWedge

macro_rules | `($x ⋏ $y) => `(binop% HWedge.hWedge $x $y)

class HVee (α β : Type*) (γ : outParam Type*) where
  hVee : α → β → γ

infixr:68 " ⋎ " => HVee.hVee

macro_rules | `($x ⋎ $y) => `(binop% HVee.hVee $x $y)

attribute [match_pattern] HTilde.hTilde HArrow.hArrow HWedge.hWedge HVee.hVee

class Tilde (α : Type*) where
  tilde : α → α

class Arrow (α : Type*) where
  arrow : α → α → α

class Wedge (α : Type*) where
  wedge : α → α → α

class Vee (α : Type*) where
  vee : α → α → α

variable {α : Type*}

@[default_instance]
instance Tilde.instHTilde [Tilde α] : HTilde α α := ⟨Tilde.tilde⟩

@[default_instance]
instance Arrow.instHArrow [Arrow α] : HArrow α α α := ⟨Arrow.arrow⟩

@[default_instance]
instance Wedge.instHWedge [Wedge α] : HWedge α α α := ⟨Wedge.wedge⟩

@[default_instance]
instance Vee.instHVee [Vee α] : HVee α α α := ⟨Vee.vee⟩

end FFL

end

section

namespace FFL

/--
A class for types with logical connectives $\top, \bot, \land, \lor, \to, \lnot$.
-/
class LogicalConnective (α : Type*) extends Tilde α, Arrow α, Wedge α, Vee α

class LogicalNeutral (α : Type*) extends Top α, Bot α

namespace LogicalConnective

section

variable {α : Type*} [LogicalConnective α]

@[match_pattern] def iff (a b : α) := (a 🡒 b) ⋏ (b 🡒 a)

/--
A defined logical connective for "iff", defined from the logical connectives `🡒` and `⋏`.
-/
infix:61 " 🡘 " => LogicalConnective.iff

end

variable (α β γ : Type*)
  [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]
  [LogicalNeutral α] [LogicalNeutral β] [LogicalNeutral γ]

structure Hom where
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ φ, toTr (∼φ) = ∼toTr φ
  map_imply' : ∀ φ ψ, toTr (φ 🡒 ψ) = toTr φ 🡒 toTr ψ
  map_and' : ∀ φ ψ, toTr (φ ⋏ ψ) = toTr φ ⋏ toTr ψ
  map_or'  : ∀ φ ψ, toTr (φ ⋎ ψ) = toTr φ ⋎ toTr ψ

/--
A structure for homomorphisms (for logical connectives) from `α` to `β`.
-/
infix:25 " →ˡᶜ " => Hom

namespace Hom

variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toTr
  coe_injective := by
    intro f g h; rcases f; rcases g; simpa using h

end Hom

end LogicalConnective

end FFL

open FFL

namespace Matrix

section conjunction

variable {α : Type*} [Top α] [Wedge α]

/-- The conjunction of a vector of elements of type `α`, where `α` is a type with `Wedge α`. -/
def conj : {n : ℕ} → (Fin n → α) → α
  |     0, _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)

end conjunction

end Matrix

namespace Multiset

variable {α : Type*} [Tilde α]

instance : Tilde (Multiset α) := ⟨fun Γ ↦ Γ.map (∼·)⟩

end Multiset

end

section

namespace FFL

/-- Entailment relation on proof system `S` and formula `F` -/
class Entailment (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*

infix:45 " ⊢! " => Entailment.Prf

namespace Entailment

variable {F : Type*} {S T U : Type*} [Entailment S F] [Entailment T F] [Entailment U F]

section

variable (𝓢 : S)

/-- Proposition that states `φ` is provable. -/
def Provable (φ : F) : Prop := Nonempty (𝓢 ⊢! φ)

/-- Abbreviation for unprovability. -/
abbrev Unprovable (φ : F) : Prop := ¬Provable 𝓢 φ

infix:45 " ⊬ " => Unprovable

end

end Entailment

end FFL

end

section

namespace FFL

namespace FirstOrder

structure Language where
  Func : Nat → Type u
  Rel  : Nat → Type u

namespace Language

protected class Eq (L : Language) where
  eq : L.Rel 2

protected class Mem (L : Language) where
  mem : L.Rel 2

end Language

end FirstOrder

end FFL

end

section

namespace FFL

namespace FirstOrder

/--
A semiterm of language `L`, with bound variables indexed by `Fin n` and free variables indexed by `ξ`. In `FFL.FirstOrder.Semiformula`, bound variables are de Bruijn indices with a separate type from free variables.
-/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity : ℕ}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n

/-- `&x` is the free variable indexed by the element `x : ξ`. -/
scoped prefix:max "&" => Semiterm.fvar

/-- `#x` is the bound variable with de Bruijn index `x`. -/
scoped prefix:max "#" => Semiterm.bvar

abbrev ClosedSemiterm (L : Language) (n : ℕ) := Semiterm L Empty n

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

section freeVariables

variable [DecidableEq ξ]

/--
The set of free variables occuring in a semiterm.
-/
def freeVariables : Semiterm L ξ n → Finset ξ
  |       #_ => ∅
  |       &x => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)

end freeVariables

end Semiterm

end FirstOrder

end FFL

end

section

namespace FFL

namespace FirstOrder

class UnivQuantifier (α : ℕ → Type*) where
  all {n : ℕ} : α (n + 1) → α n

prefix:64 "∀¹ " => UnivQuantifier.all

class ExsQuantifier (α : ℕ → Type*) where
  exs {n : ℕ} : α (n + 1) → α n

prefix:64 "∃¹ " => ExsQuantifier.exs

attribute [match_pattern] UnivQuantifier.all ExsQuantifier.exs

class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  connectives : (n : ℕ) → LogicalConnective (α n)
  neutrals : (n : ℕ) → LogicalNeutral (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalNeutral (α n) := LCWQ.neutrals n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)]
    [(n : ℕ) → LogicalNeutral (α n)] : LCWQ α where
  connectives := inferInstance
  neutrals := inferInstance

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]
variable {n : ℕ}

def allClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => allClosure (∀¹ a)

/--
The universal closure of a formula.
-/
prefix:64 "∀¹* " => allClosure

def allItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => allItr k (∀¹ a)

notation "∀¹^[" k "] " φ:64 => allItr k φ

end UnivQuantifier

section quantifier

variable {α : ℕ → Type*} {n : ℕ}

def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∀¹ (φ 🡒 ψ)

def bexs [ExsQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃¹ (φ ⋏ ψ)

/-- A bounded universal quantifier. `∀¹[φ] ψ` is defined as `∀¹ (φ 🡒 ψ)`. -/
notation:64 "∀¹[" φ "] " ψ => ball φ ψ

/-- A bounded existential quantifier. `∃¹[φ] ψ` is defined as `∃¹ (φ ⋏ ψ)`. -/
notation:64 "∃¹[" φ "] " ψ => bexs φ ψ

end quantifier

end FirstOrder

end FFL

end

section

namespace FFL.FirstOrder

/--
A semiformula of language `L`. Free variables are of type `ξ`, and bound variables are implemented as de Bruijn indices, of a type `Fin n` separate from free variables.
-/
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |  verum {n : ℕ} : Semiformula L ξ n
  | falsum {n : ℕ} : Semiformula L ξ n
  |    rel : {n arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {n arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and {n : ℕ} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or {n : ℕ} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all {n : ℕ} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs {n : ℕ} : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Sentence (L : Language) := Formula L Empty

abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

abbrev Semiproposition (L : Language) (n : ℕ) := Semiformula L ℕ n

abbrev Proposition (L : Language) := Semiproposition L 0

namespace Semiformula

variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  |    verum => falsum
  |   falsum => verum
  |  rel r v => nrel r v
  | nrel r v => rel r v
  |  and φ ψ => or (neg φ) (neg ψ)
  |   or φ ψ => and (neg φ) (neg ψ)
  |    all φ => exs (neg φ)
  |    exs φ => all (neg φ)

instance : LogicalConnective (Semiformula L ξ n) where
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  tilde := neg

instance : LogicalNeutral (Semiformula L ξ n) where
  top := verum
  bot := falsum

instance : Quantifier (Semiformula L ξ) where
  all := all
  exs := exs

section FreeVariables

variable [DecidableEq ξ]

def freeVariables {n} : Semiformula L ξ n → Finset ξ
  |  rel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  |        ⊤ => ∅
  |        ⊥ => ∅
  |    φ ⋏ ψ => freeVariables φ ∪ freeVariables ψ
  |    φ ⋎ ψ => freeVariables φ ∪ freeVariables ψ
  |     ∀¹ φ => freeVariables φ
  |     ∃¹ φ => freeVariables φ

def fvSup (φ : Semiproposition L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ

end FreeVariables

end Semiformula

abbrev Theory (L : Language) := Set (Sentence L)

end FFL.FirstOrder

end

section

namespace FFL

namespace FirstOrder

/--
A structure for maps which rewrite the semiterms occurring in a term.

toFun - A function from `Semiterm L ξ₁ n₁` to `Semiterm L ξ₂ n₂`.

func'' - A proof that `toFun` respects the function symbols of `L`.
-/
structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func'' {k : ℕ} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    toFun (Semiterm.func f v) = Semiterm.func f fun i ↦ toFun (v i)

abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective := fun f g h => by rcases f; rcases g; simpa using h

protected def id : Rew L ξ n ξ n where
  toFun := id
  func'' := fun _ _ => rfl

protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func'' := fun f v ↦
    (congrArg ω₂ (ω₁.func'' f v)).trans (ω₂.func'' f (fun i ↦ ω₁ (v i)))

def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  |       #x => b x
  |       &x => e x
  | func f v => func f (fun i => bindAux b e (v i))

/-- `FFL.FirstOrder.Rew.bind f` is a substitution of the bound variables occurring in a term by `b : Fin n₁ → Semiterm L ξ₂ n₂`, and the free variables occurring in a term by `e : ξ₁ → Semiterm L ξ₂ n₂`. -/
def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func'' := fun _ _ => rfl

def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

/-- `FFL.FirstOrder.Rew.subst v` is a substitution of the bound variables occurring in a term by `v : Fin n → Semiterm L ξ n'`. -/
def subst {n' : ℕ} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' :=
  bind v fvar

/-- `FFL.FirstOrder.Rew.emb` is a embedding of a term with no free variables. It can be thought of as a cast from `Semiterm L Empty n` to `Semiterm L ξ n` for any type `ξ`. -/
def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim

/-- `FFL.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in a term by `#x ↦ #(Fin.succ x)`. -/
def bShift : Rew L ξ n ξ (n + 1) :=
  map Fin.succ id

protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

section Syntactic

/-- `FFL.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦ &(x + 1)`. -/
def shift : SyntacticRew L n n := map id Nat.succ

def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

def fixitr (n : ℕ) : (m : ℕ) → SyntacticRew L n (n + m)
  |     0 => Rew.id
  | m + 1 => Rew.fix.comp (fixitr n m)

end Syntactic

end Rew

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

def toEmpty [DecidableEq ξ] {n : ℕ} : (t : Semiterm L ξ n) → t.freeVariables = ∅ → ClosedSemiterm L n
  |       #x, _ => #x
  |       &x, h => False.elim (by simp [freeVariables] at h)
  | func f v, h =>
    have : ∀ i, (v i).freeVariables = ∅ := fun i ↦ Finset.subset_empty.mp
        (h ▸ Finset.subset_biUnion_of_mem (fun j ↦ (v j).freeVariables) (Finset.mem_univ i))
    func f fun i ↦ toEmpty (v i) (this i)

end Semiterm

/--
A typeclass for `Rew`s which additionally respect quantifiers.

`app` - A notion of application of `Rew`s to formulas.

`app_all` - Application preserves universal quantification.

`app_exs` - Application preserves existential quantification.
-/
class Rewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] where
  app {n₁ n₂ : ℕ} : Rew L ξ n₁ ζ n₂ → F n₁ →ˡᶜ G n₂
  app_all {n₁ n₂ : ℕ} (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ : F (n₁ + 1)) :
    app ω₁₂ (∀¹ φ) = ∀¹ (app ω₁₂.q φ)
  app_exs {n₁ n₂ : ℕ} (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ : F (n₁ + 1)) :
    app ω₁₂ (∃¹ φ) = ∃¹ (app ω₁₂.q φ)

namespace Rewriting

variable {F : ℕ → Type _} {G : ℕ → Type _}
  {L : Language} {ξ : Type _} {ζ : Type _}
variable [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G]
variable {n₁ n₂ n : ℕ}

/-- Application of a `Rewriting` to a formula. -/
infixr:73 " ▹ " => app

abbrev subst [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ := Rew.subst w ▹ φ

/-- Applies the substitution `FFL.FirstOrder.Rew.subst w` to a formula. This substitutes the bound variables occurring in the formula by `w : Fin n₁ → Semiterm L ξ n₂`. -/
infix:90 " ⇜ " => FFL.FirstOrder.Rewriting.subst

/-- Applies the substitution `FFL.FirstOrder.Rew.shift` to a formula. This substitutes each free variable `&x` with `&(x + 1)`. -/
abbrev shift [Rewriting L ℕ F ℕ F] : F n →ˡᶜ F n := app Rew.shift

abbrev free [Rewriting L ℕ F ℕ F] : F (n + 1) →ˡᶜ F n := app Rew.free

def shifts [Rewriting L ℕ F ℕ F] (Γ : Multiset (F n)) : Multiset (F n) := Γ.map Rewriting.shift

scoped[FFL.FirstOrder] postfix:max "⁺" => FirstOrder.Rewriting.shifts

abbrev emb {ο : Type _} {ξ : Type _} [IsEmpty ο] {O F : ℕ → Type*}
    [LCWQ O] [LCWQ F] [Rewriting L ο O ξ F] : O n →ˡᶜ F n := app (Rew.emb (ξ := ξ))

end Rewriting

section Notation

syntax (name := substNotation) term:max "/[" term,* "]" : term

/-- Slash notation for rewriting bound variables of a formula.

The notation `φ/w` is equivalent to `φ ⇜ w`, which for a formula `φ` with bound variables from `Fin n₁`, substitutes the bound variables occurring in `φ` by `w : Fin n₁ → Semiterm L ξ n₂`. -/
macro_rules (kind := substNotation)
  | `($φ:term /[$terms:term,*]) => `($φ ⇜ ![$terms,*])

end Notation

end FirstOrder

end FFL

end

section

namespace FFL

namespace FirstOrder

namespace Semiformula

variable {L : Language} {ξ₁ : Type _} {n₁ : ℕ} {ξ₂ : Type _} {n₂ : ℕ}
  {ξ : Type _} {ζ : Type _} {n : ℕ}

def rewAux ⦃n₁ n₂ : ℕ⦄ (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |  rel r v => rel r (ω ∘ v)
  | nrel r v => nrel r (ω ∘ v)
  |    φ ⋏ ψ => rewAux ω φ ⋏ rewAux ω ψ
  |    φ ⋎ ψ => rewAux ω φ ⋎ rewAux ω ψ
  |     ∀¹ φ => ∀¹ rewAux ω.q φ
  |     ∃¹ φ => ∃¹ rewAux ω.q φ

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ →ˡᶜ Semiformula L ξ₂ n₂ where
  toTr := rewAux ω
  map_top' := by rfl
  map_bot' := by rfl
  map_neg' := fun φ ↦ by
    change rewAux ω (neg φ) = neg (rewAux ω φ)
    induction φ generalizing n₂ <;> simp_all [rewAux, neg] <;> rfl
  map_and' := fun φ ψ ↦ rfl
  map_or' := fun φ ψ ↦ rfl
  map_imply' := fun φ ψ ↦ by
    change or (rewAux ω (neg φ)) (rewAux ω ψ) =
      or (neg (rewAux ω φ)) (rewAux ω ψ)
    congr 1
    induction φ generalizing n₂ <;> simp_all [rewAux, neg] <;> rfl

instance : Rewriting L ξ (Semiformula L ξ) ζ (Semiformula L ζ) where
  app := rew
  app_all (_ _) := rfl
  app_exs (_ _) := rfl

abbrev free (φ : Semiproposition L (n + 1)) : Semiproposition L n := Rewriting.free φ

section univCl

def univCl' (φ : Proposition L) : Proposition L := ∀¹* (@Rew.fixitr L 0 φ.fvSup ▹ φ)

section

variable {ξ : Type _} {L : Language}

def toEmpty [DecidableEq ξ] {n : ℕ} : (φ : Semiformula L ξ n) → φ.freeVariables = ∅ → Semisentence L n
  |  rel R v, h => rel R fun i ↦ (v i).toEmpty <| Finset.subset_empty.mp
      (h ▸ Finset.subset_biUnion_of_mem (fun j ↦ (v j).freeVariables) (Finset.mem_univ i))
  | nrel R v, h => nrel R fun i ↦ (v i).toEmpty <| Finset.subset_empty.mp
      (h ▸ Finset.subset_biUnion_of_mem (fun j ↦ (v j).freeVariables) (Finset.mem_univ i))
  |        ⊤, _ => ⊤
  |        ⊥, _ => ⊥
  |    φ ⋏ ψ, h =>
    φ.toEmpty ((Finset.union_eq_empty.mp h).1) ⋏
    ψ.toEmpty ((Finset.union_eq_empty.mp h).2)
  |    φ ⋎ ψ, h =>
    φ.toEmpty ((Finset.union_eq_empty.mp h).1) ⋎
    ψ.toEmpty ((Finset.union_eq_empty.mp h).2)
  |     ∀¹ φ, h => ∀¹ φ.toEmpty (h)
  |     ∃¹ φ, h => ∃¹ φ.toEmpty (h)

end

/-- An universal closure of formula -/
def univCl (φ : Proposition L) : Sentence L := φ.univCl'.toEmpty (by
  have term_closed {n m : ℕ} (ω : SyntacticRew L n m) (t : Semiterm L ℕ n)
      (hb : ∀ x, (ω #x).freeVariables = ∅)
      (hf : ∀ x ∈ t.freeVariables, (ω &x).freeVariables = ∅) :
      (ω t).freeVariables = ∅ := by
    induction t with
    | bvar x => exact hb x
    | fvar x => exact hf x (by simp [Semiterm.freeVariables])
    | func f v ih =>
      change (ω.toFun (Semiterm.func f v)).freeVariables = ∅
      rw [ω.func'']
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      have hi' := ih i (fun y hy ↦ hf y
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩))
      exact Finset.notMem_empty x (hi' ▸ hi)

  have shift_closed {n : ℕ} (t : Semiterm L ℕ n) (h : t.freeVariables = ∅) :
      (Rew.bShift t).freeVariables = ∅ :=
    term_closed Rew.bShift t (fun _ ↦ rfl)
      (fun x hx ↦ False.elim (Finset.notMem_empty x (h ▸ hx)))

  have q_closed {n m : ℕ} (ω : SyntacticRew L n m)
      (hb : ∀ x, (ω #x).freeVariables = ∅) :
      ∀ x, (ω.q #x).freeVariables = ∅ := by
    intro x
    cases x using Fin.cases with
    | zero => rfl
    | succ x => exact shift_closed (ω #x) (hb x)

  have formula_closed {n m : ℕ} (φ : Semiproposition L n) (ω : SyntacticRew L n m)
      (hb : ∀ x, (ω #x).freeVariables = ∅)
      (hf : ∀ x ∈ φ.freeVariables, (ω &x).freeVariables = ∅) :
      (Semiformula.rewAux ω φ).freeVariables = ∅ := by
    induction φ generalizing m with
    | verum => rfl
    | falsum => rfl
    | rel R v | nrel R v =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      have hi' := term_closed ω (v i) hb (fun y hy ↦ hf y
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩))
      exact Finset.notMem_empty x (hi' ▸ hi)
    | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
      exact Finset.union_eq_empty.mpr
        ⟨ihφ ω hb (fun x hx ↦ hf x (Finset.mem_union_left _ hx)),
         ihψ ω hb (fun x hx ↦ hf x (Finset.mem_union_right _ hx))⟩
    | all φ ih | exs φ ih =>
      exact ih ω.q (q_closed ω hb) (fun x hx ↦ shift_closed (ω &x) (hf x hx))

  have lt_fvSup_of_mem {n : ℕ} {φ : Semiproposition L n} {x : ℕ}
      (hx : x ∈ φ.freeVariables) : x < φ.fvSup := by
    obtain ⟨m, hm⟩ := Finset.max_of_mem hx
    simpa only [Semiformula.fvSup, hm, WithBot.recBotCoe_coe] using
      Nat.lt_succ_of_le (Finset.le_max_of_eq hx hm)

  have freeVariables_allClosure {n : ℕ} (φ : Semiproposition L n) :
      (∀¹* φ).freeVariables = φ.freeVariables := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih (∀¹ φ)

  have fixitr_fvar (n m x : ℕ) :
      Rew.fixitr n m (&x : Semiterm L ℕ n) =
        if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      change Rew.fix (Rew.fixitr n m &x) = _
      rw [ih]
      by_cases hx : x < m
      · have hx' : x < m + 1 := by omega
        simp only [dif_pos hx, dif_pos hx']
        rfl
      · by_cases hx' : x < m + 1
        · have he : x = m := by omega
          subst x
          simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]
          rfl
        · have he : x - m = x - (m + 1) + 1 := by omega
          simp only [dif_neg hx, dif_neg hx', he]
          rfl
  change (∀¹* (Semiformula.rewAux (Rew.fixitr 0 φ.fvSup) φ)).freeVariables = ∅
  rw [freeVariables_allClosure]
  exact formula_closed φ (Rew.fixitr 0 φ.fvSup) (fun x ↦ Fin.elim0 x) (fun x hx ↦ by
    simp [fixitr_fvar, lt_fvSup_of_mem hx, Semiterm.freeVariables]))

end univCl

end Semiformula

end FirstOrder

end FFL

end

section

namespace FFL

namespace FirstOrder

variable {L : Language} {ξ : Type _} {n : ℕ}

namespace Semiformula

structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Semisentence L n

namespace Operator

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiformula L ξ n :=
  Rewriting.emb o.sentence ⇜ v

protected class Eq (L : Language) where
  eq : Semiformula.Operator L 2

protected class Mem (L : Language) where
  mem : Semiformula.Operator L 2

notation "op(=)" => Operator.Eq.eq

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩

instance [L.Mem] : Operator.Mem L := ⟨⟨Semiformula.rel Language.Mem.mem Semiterm.bvar⟩⟩

end Operator

def ballMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

def bexsMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

end Semiformula

end FirstOrder

end FFL

end

section

open Lean Elab PrettyPrinter Delaborator SubExpr

namespace Lean.TSyntax

variable {m : Type → Type}

meta def freshIdent [Monad m] [MonadQuotation m] : m (TSyntax `ident) := do
  let name ← Term.mkFreshBinderName
  return ⟨mkIdent name⟩

end Lean.TSyntax

namespace FFL.FirstOrder

namespace Semiformula

variable {L : Language} {ξ : Type*} {n m : ℕ}

/-- `nestFormulae φ(x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ ((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`, and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining bound variables, while all of the original `n` bound variables of `φ` get bounded to a `∀` quantifier.

Intuitively, nestFormulae gives `R(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting functions `f₁, … fₙ` into a relation `R`, using the defining formulae of their graphs (`xᵢ = fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `R(x₁,…,xₙ)` iff `φ(x₁,…,xₙ)`). -/
def nestFormulae (φ : Semiformula L ξ n) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ m :=
  let σ : Semiformula L ξ (m + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m) :> fun j ↦ #(j.addNat n))) 🡒
      Rewriting.subst φ fun i ↦ #(i.addCast m)
  ∀¹^[n] σ

/-- `nestFormulaeFunc φ(x,x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ ((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x,x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`, and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining bound variables plus `x`, while all of the original bound variables `x₁,…,xₙ` get bounded to a `∀` quantifier.

Intuitively, nestFormulaeFunc gives `F(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting functions `f₁, … fₙ` into a function `F`, using the defining formulae of their graphs (`xᵢ = fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `x = F(x₁,…,xₙ)` iff `φ(x,x₁,…,xₙ)`). -/
def nestFormulaeFunc (φ : Semiformula L ξ (n + 1)) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ (m + 1) :=
  let σ : Semiformula L ξ ((m + 1) + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m.succ) :> fun j ↦ #(j.succ.addNat n))) 🡒
      Rewriting.subst φ (#((0 : Fin (m + 1)).addNat n) :> fun i ↦ #(i.addCast m.succ))
  ∀¹^[n] σ

end Semiformula

namespace BinderNotation

@[simp] abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ

declare_syntax_cat first_order_term

declare_syntax_cat first_order.quote_type

syntax:max "lit" : first_order.quote_type

syntax:max "faf" : first_order.quote_type

syntax "⤫term(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_term:0 "]" : term

syntax "(" first_order_term ")" : first_order_term

syntax:max ident : first_order_term

syntax:max "#" term:max : first_order_term

syntax:max "&" term:max : first_order_term

syntax:80 "!" term:max first_order_term:81* (" ⋯")? : first_order_term

macro_rules
  | `(⤫term($type)[ $binders* | $fbinders* | ($e) ]) => `(⤫term($type)[ $binders* | $fbinders* | $e ])

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(⤫term(lit)[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(⤫term(lit)[ $_*       | $_*        | &$x:term   ]) => `(&$x)

open Semiformula

declare_syntax_cat first_order_formula

syntax "⤫formula(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_formula:0 "]" : term

syntax "(" first_order_formula ")" : first_order_formula

syntax:60 "!" term:max first_order_term:61* ("⋯")? : first_order_formula

syntax:32 first_order_formula:33 " ∧ " first_order_formula:32 : first_order_formula

syntax:30 first_order_formula:31 " ∨ " first_order_formula:30 : first_order_formula

syntax:max "¬" first_order_formula:35 : first_order_formula

syntax:10 first_order_formula:9 " → " first_order_formula:10 : first_order_formula

syntax:5 first_order_formula " ↔ " first_order_formula : first_order_formula

syntax:max "∀ " ident+ ", " first_order_formula:0 : first_order_formula

syntax:max "∃ " ident+ ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ($e)          ]) => `(⤫formula($type)[ $binders* | $fbinders* | $e ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∧ $ψ       ]) => `(@HWedge.hWedge _ _ _ Wedge.instHWedge ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∨ $ψ       ]) => `(@HVee.hVee _ _ _ Vee.instHVee ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ¬$φ           ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ → $ψ       ]) => `(@HArrow.hArrow _ _ _ Arrow.instHArrow ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ↔ $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] 🡘 ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀¹ $ψ))
    return s
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃¹ $ψ))
    return s

/--
A formula in literal notation. For a formula `φ`, write `!φ` to include `φ` in the formula. Identifiers may be written after `!φ` as its bound variables.

`⋯` adds enough unnamed bound variables to fill up the arity of `φ`, with indices starting after the last named identifier. For example, assume `φ` is a `Semiformula L k`, and consider the formula `“x y z. !φ x y ⋯”`. Here `x`, `y`, and `z` are the bound variables `#0`, `#1`, and `#2` respectively. Then `!φ x y ⋯` will add `k - 2` new bound variables, and expand to `!φ #0 #1 #3 #4 ... #(k + 1)`.
-/
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a ] :> $s))
    `($φ ⇜ $v)
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `($φ ⇜ $v)

syntax "“" ident* "| "  first_order_formula:0 "”" : term

syntax "“" ident* ". "  first_order_formula:0 "”" : term

syntax "“" first_order_formula:0 "”" : term

macro_rules
  | `(“ $e:first_order_formula ”)              => `(⤫formula(lit)[           |            | $e ])
  | `(“ $binders*. $e:first_order_formula ”)   => `(⤫formula(lit)[ $binders* |            | $e ])
  | `(“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(lit)[           | $fbinders* | $e ])

syntax:45 first_order_term:45 " = " first_order_term:0 : first_order_formula

syntax:45 first_order_term:45 " ∈ " first_order_term:0 : first_order_formula

syntax:45 first_order_term:45 " ≠ " first_order_term:0 : first_order_formula

syntax:45 first_order_term:45 " ∉ " first_order_term:0 : first_order_formula

syntax:max "∀ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula

syntax:max "∃ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a ] :> $s)
    `(($φ).nestFormulae $Ψ)
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a] :> $s)
    `(($φ).nestFormulae $Ψ)

macro_rules
  | `(⤫term(faf)[ $binders* | $fbinders* | $x:ident                         ]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable does not appeared."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(“#0 = &$i”)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(“#0 = #$i”)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a ] :> $s)
    `(($f).nestFormulaeFunc $Ψ)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ “#0 = #(finSuccItr x $length)”)) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a] :> $s)
    `(($f).nestFormulaeFunc $Ψ)

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 = #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ≠ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ∈ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ∉ #0”)))

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.ballMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.bexsMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))

syntax "f“" ident* "| "  first_order_formula:0 "”" : term

syntax "f“" ident* ". "  first_order_formula:0 "”" : term

syntax "f“" first_order_formula:0 "”" : term

/-- A formula in formula-as-function notation. Use `f“⋯. ⋯”` for bound variables, and `f“⋯ | ⋯”` for free variables. -/
macro_rules
  | `(f“ $e:first_order_formula ”)              => `(⤫formula(faf)[           |            | $e ])
  | `(f“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(faf)[           | $fbinders* | $e ])
  | `(f“ $binders*. $e:first_order_formula ”)   => `(⤫formula(faf)[ $binders* |            | $e ])

end BinderNotation

end FFL.FirstOrder

end

section

namespace FFL

namespace OneSidedLK

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]

abbrev Pullback (𝔇 : Multiset F → Type*) {G : Type*} [LogicalConnective G]
    [LogicalNeutral G] (f : G →ˡᶜ F) : Multiset G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)

end OneSidedLK

end FFL

end

section

namespace FFL

namespace FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := Multiset (Proposition L)

/-- Derivation for $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| identity {k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ℕ 0) : Derivation ⦃.rel r v, .nrel r v⦄
| cut {Γ : Sequent L} {φ : Proposition L} {Δ : Sequent L} :
    Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction {Δ Γ : Sequent L} : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or {Γ : Multiset (Proposition L)} {φ ψ : Proposition L} :
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃φ, ψ⦄) →
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃φ ⋎ ψ⦄)
| and {Γ : Multiset (Proposition L)} {φ ψ : Proposition L} :
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃φ⦄) →
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃ψ⦄) →
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃φ ⋏ ψ⦄)
| all {Γ : Multiset (Semiproposition L 0)} {φ : Semiproposition L (0 + 1)} :
    Derivation (HAdd.hAdd (γ := Sequent L) Γ⁺ ⦃φ.free⦄) →
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃∀¹ φ⦄)
| exs {Γ : Multiset (Semiproposition L 0)} {φ : Semiproposition L (Nat.succ 0)}
    {t : Semiterm L ℕ 0} :
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃φ/[t]⦄) →
    Derivation (HAdd.hAdd (γ := Sequent L) Γ ⦃∃¹ φ⦄)

structure Theory.Proof (T : Theory L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation Rewriting.emb (⦃σ⦄ + ∼axioms)

namespace Theory.Proof

instance : Entailment (Theory L) (Sentence L) where
  Prf := Theory.Proof

end Theory.Proof

end FirstOrder

end FFL

end

section

namespace FFL

namespace FirstOrder

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]
variable {n : ℕ}

namespace Theory

section Eq

variable (L)

abbrev Eq.refl : Sentence L := “∀ x, x = x”

abbrev Eq.symm : Sentence L := “∀ x y, x = y → y = x”

abbrev Eq.trans : Sentence L := “∀ x y z, x = y → y = z → x = z”

variable {L}

abbrev Eq.funcExt {k : ℕ} (f : L.Func k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      op(=).operator ![Semiterm.func f (fun i ↦ #(i.addCast k)), Semiterm.func f (fun i ↦ #(i.addNat k))]
  ∀¹* σ

abbrev Eq.relExt {k : ℕ} (r : L.Rel k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      Semiformula.rel r (fun i ↦ #(i.addCast k)) 🡒 Semiformula.rel r (fun i ↦ #(i.addNat k))
  ∀¹* σ

variable (L)

inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k : ℕ} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k : ℕ} (r : L.Rel k) : eqAxiom (Eq.relExt r)

notation "𝗘𝗤" => eqAxiom

end Eq

end Theory

namespace Semiformula

def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”

prefix:64 "∃¹! " => existsUnique

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∃! " first_order_formula:0 : first_order_formula

syntax:max "∃! " ident ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $φ:first_order_formula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ ])

end BinderNotation

end FirstOrder

end FFL

end

section

namespace FFL.FirstOrder

namespace Language

namespace Set

abbrev Func : ℕ → Type := fun _ ↦ Empty

inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2

end Set

/-- Language of set theory -/
@[reducible]
def set : Language where
  Func := Set.Func
  Rel := Set.Rel

notation "ℒₛₑₜ" => set

namespace Set

instance : (ℒₛₑₜ).Eq := ⟨Rel.eq⟩

instance : (ℒₛₑₜ).Mem := ⟨Rel.mem⟩

end Set

end Language

abbrev SetTheory := Theory ℒₛₑₜ

abbrev SetTheorySemisentence (n : ℕ) := Semisentence ℒₛₑₜ n

abbrev SetTheorySentence := Sentence ℒₛₑₜ

abbrev SetTheorySemiproposition (n : ℕ) := Semiproposition ℒₛₑₜ n

end FFL.FirstOrder

end

section

namespace FFL.FirstOrder.SetTheory

def isSubsetOf : SetTheorySemisentence 2 := “x y. ∀ z ∈ x, z ∈ y”

syntax:45 first_order_term:45 " ⊆ " first_order_term:0 : first_order_formula

open Lean Elab PrettyPrinter Delaborator SubExpr in
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ⊆ $u:first_order_term ]) =>
    `(⤫formula($type)[ $binders* | $fbinders* | !isSubsetOf $t:first_order_term $u:first_order_term ])

def isEmpty : SetTheorySemisentence 1 := “x. ∀ y, y ∉ x”

def isNonempty : SetTheorySemisentence 1 := “x. ∃ y, y ∈ x”

def isSucc : SetTheorySemisentence 2 := “y x. ∀ z, z ∈ y ↔ z = x ∨ z ∈ x”

namespace Axiom

/-- Axiom of empty set. -/
def empty : SetTheorySentence := “∃ e, ∀ y, y ∉ e”

/-- Axiom of extentionality. -/
def extentionality : SetTheorySentence := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”

/-- Axiom of pairing. -/
def pairing : SetTheorySentence := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”

/-- Axiom of union. -/
def union : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”

/-- Axiom of power set. -/
def power : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”

/-- Axiom of infinity. -/
def infinity : SetTheorySentence := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”

/-- Axiom of foundation. -/
def foundation : SetTheorySentence := “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

/-- Axiom schema of separation (Aussonderungsaxiom). -/
def separationSchema (φ : SetTheorySemiproposition 1) : SetTheorySentence :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

/-- Axiom schema of replacement. -/
def replacementSchema (φ : SetTheorySemiproposition 2) : SetTheorySentence :=
  .univCl “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

/-- Axiom of choice. -/
def choice : SetTheorySentence :=
  “∀ 𝓧, (∀ X ∈ 𝓧, !isNonempty X) ∧ (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y) → ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X”

end Axiom

/-- Zermelo-Fraenkel set theory. -/
inductive ZermeloFraenkel : SetTheory
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, ZermeloFraenkel φ
  /-- Axiom of empty set. -/
  | axiom_of_empty_set : ZermeloFraenkel Axiom.empty
  /-- Axiom of extentionality. -/
  | axiom_of_extentionality : ZermeloFraenkel Axiom.extentionality
  /-- Axiom of pairing. -/
  | axiom_of_pairing : ZermeloFraenkel Axiom.pairing
  /-- Axiom of union. -/
  | axiom_of_union : ZermeloFraenkel Axiom.union
  /-- Axiom of power set. -/
  | axiom_of_power_set : ZermeloFraenkel Axiom.power
  /-- Axiom of infinity. -/
  | axiom_of_infinity : ZermeloFraenkel Axiom.infinity
  /-- Axiom of foundation. -/
  | axiom_of_foundation : ZermeloFraenkel Axiom.foundation
  /-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SetTheorySemiproposition 1) : ZermeloFraenkel (Axiom.separationSchema φ)
  /-- Axiom schema of replacement. -/
  | axiom_of_replacement (φ : SetTheorySemiproposition 2) : ZermeloFraenkel (Axiom.replacementSchema φ)

notation "𝗭𝗙" => ZermeloFraenkel

/-- AC: Axiom of choice. -/
def AxiomOfChoice : SetTheory := {Axiom.choice}

notation "𝗔𝗖" => AxiomOfChoice

/-- Zermelo-Fraenkel set theory with axiom of choice. -/
abbrev ZermeloFraenkelChoice : SetTheory := 𝗭𝗙 ∪ 𝗔𝗖

notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice

end FFL.FirstOrder.SetTheory

end

section

namespace FFL.FirstOrder.SetTheory

def doubleton.dfn : SetTheorySemisentence 3 := “p x y. ∀ z, z ∈ p ↔ z = x ∨ z = y”

def singleton.dfn : SetTheorySemisentence 2 := “p x. !doubleton.dfn p x x”

def sUnion.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w”

def union.dfn : SetTheorySemisentence 3 := “u x y. ∀ d, !doubleton.dfn d x y → !sUnion.dfn u d”

def insert.dfn : SetTheorySemisentence 3 := “u x y. ∀ s, !singleton.dfn s x → !union.dfn u s y”

def sInter.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ !isNonempty x ∧ ∀ y ∈ x, z ∈ y”

def kpair.dfn : SetTheorySemisentence 3 :=
  “k x y. ∀ x', !singleton.dfn x' x → ∀ z, !doubleton.dfn z x y → !doubleton.dfn k x' z”

def kpair.π₁.dfn : SetTheorySemisentence 2 := “p₁ x. ∀ i, !sInter.dfn i x → !sUnion.dfn p₁ i”

def kpair.π₂.dfn : SetTheorySemisentence 2 :=
  “p₂ x. ∀ u, !sUnion.dfn u x → ∀ i, !sInter.dfn i x → ∀ s, (∀ z, z ∈ s ↔ (z ∈ u ∧ (z ∈ i → u = i))) → !sUnion.dfn p₂ s”

def prod.dfn : SetTheorySemisentence 3 := “p X Y. ∀ z, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, !kpair.dfn z x y”

abbrev succ.dfn := isSucc

def IsInductive.dfn : SetTheorySemisentence 1 :=
  “x. (∀ e, !isEmpty e → e ∈ x) ∧ (∀ y ∈ x, ∀ y', !succ.dfn y' y → y' ∈ x)”

def isω : SetTheorySemisentence 1 := “ω. ∀ x, x ∈ ω ↔ ∀ I, !IsInductive.dfn I → x ∈ I”

end FFL.FirstOrder.SetTheory

end

section

namespace FFL.FirstOrder.SetTheory

section range

def range.dfn : SetTheorySemisentence 2 := f“r R. ∀ y, y ∈ r ↔ ∃ x, !kpair.dfn x y ∈ R”

end range

def function.dfn : SetTheorySemisentence 3 := f“F Y X. ∀ f, f ∈ F ↔ f ⊆ !prod.dfn X Y ∧ ∀ x ∈ X, ∃! y, !kpair.dfn x y ∈ f”

def IsFunction.dfn : SetTheorySemisentence 1 := f“f. ∃ X Y, f ∈ !function.dfn Y X”

def value.dfn : SetTheorySemisentence 3 := f“v f x. ∀ z, z ∈ v ↔ z ∈ !sUnion.dfn (!range.dfn f) ∧ ∃ y, z ∈ y ∧ !kpair.dfn x y ∈ f”

end FFL.FirstOrder.SetTheory

end

end FormalizedFormalLogic

namespace Constant14

open FFL FFL.FirstOrder Turing BusyBeaver FFL.FirstOrder.SetTheory

section BackgroundDefs

/-- `O` is the least set containing `x` and closed under `f`. -/
def orbit : SetTheorySemisentence 3 :=
  f“O f x. !IsFunction.dfn f ∧
    ∀ z, z ∈ O ↔ ∀ A, (x ∈ A ∧ ∀ y ∈ A, !value.dfn f y ∈ A) → z ∈ A”

/-- The von Neumann ordinal `0 = ∅`. -/
def zero : SetTheorySemisentence 1 :=
  “zero. !isEmpty zero”

/-- The graph formula for the von Neumann numeral associated with a Lean `n : ℕ`. -/
def numeral : ℕ → SetTheorySemisentence 1
  | 0     => “zero. !isEmpty zero”
  | n + 1 => succ.dfn.nestFormulaeFunc ![numeral n]

/--
`⟨0,n⟩` represents `n`, while `⟨1,n⟩` represents `-(n+1)`.
-/
def integers : SetTheorySemisentence 1 :=
  f“Z. Z = !prod.dfn (!(numeral 2)) (!isω)”

/-- Zero in the integer encoding: `⟨0,0⟩`. -/
def integerZero : SetTheorySemisentence 1 :=
  f“z. z = !kpair.dfn (!(numeral 0)) (!(numeral 0))”

/-- Configurations with `n` state codes, an integer head position, and a binary tape. -/
def configSet (n : ℕ) : SetTheorySemisentence 1 :=
  f“Z. Z =
    !prod.dfn (!(numeral n)) (!prod.dfn (!integers) (!function.dfn (!(numeral 2)) (!integers)))”

/-- Integer successor for the encoding `⟨0,n⟩ = n`, `⟨1,n⟩ = -(n+1)`. -/
def integerSucc.dfn : SetTheorySemisentence 2 :=
  f“z' z.
    (z ∈ (!integers) ∧
      ((!kpair.π₁.dfn z = (!(numeral 0)) ∧
        z' = !kpair.dfn (!(numeral 0)) (!succ.dfn (!kpair.π₂.dfn z))) ∨
       (!kpair.π₁.dfn z = (!(numeral 1)) ∧
        ((!kpair.π₂.dfn z = (!(numeral 0)) ∧ z' = (!integerZero)) ∨
         ∃ n ∈ (!isω),
          !kpair.π₂.dfn z = !succ.dfn n ∧
          z' = !kpair.dfn (!(numeral 1)) n)))) ∨
    (z ∉ (!integers) ∧ z' = (!integerZero))”

/-- Integer predecessor for the encoding `⟨0,n⟩ = n`, `⟨1,n⟩ = -(n+1)`. -/
def integerPred.dfn : SetTheorySemisentence 2 :=
  f“z' z.
    (z ∈ (!integers) ∧ z' ∈ (!integers) ∧ !integerSucc.dfn z z') ∨
    (z ∉ (!integers) ∧ z' = (!integerZero))”

def setPair (x y : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  kpair.dfn.nestFormulaeFunc ![x, y]

def setTriple (x y z : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  setPair x (setPair y z)

def finiteSet : List (SetTheorySemisentence 1) → SetTheorySemisentence 1
  | []      => zero
  | x :: xs => insert.dfn.nestFormulaeFunc ![x, finiteSet xs]

def directionCode : Option Dir → ℕ
  | some .left  => 0
  | none        => 1
  | some .right => 2

def stateCode {n : ℕ} : Option (Fin n) → ℕ
  | some q => q.val
  | none   => n

def transitionCode {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (q : Fin n) (symbol : Fin 2) : ℕ × ℕ × ℕ :=
  match M q symbol with
  | some (q', stmt) => (stateCode q', stmt.symbol.val, directionCode (some stmt.dir))
  | none            => (n, symbol.val, directionCode none)

def transitionEntry (q symbol q' written direction : ℕ) :
    SetTheorySemisentence 1 :=
  setPair (setPair (numeral q) (numeral symbol))
    (setTriple (numeral q') (numeral written) (numeral direction))

def transitionEntries {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (SetTheorySemisentence 1) :=
  (List.ofFn fun q : Fin n ↦
    List.ofFn fun symbol : Fin 2 ↦
      letI output := transitionCode M q symbol
      transitionEntry q.val symbol.val output.1 output.2.1 output.2.2).flatten ++
  List.ofFn fun symbol : Fin 2 ↦
    transitionEntry n symbol.val n symbol.val (directionCode none)

def transitionDomain (n : ℕ) : SetTheorySemisentence 1 :=
  prod.dfn.nestFormulaeFunc ![numeral (n + 1), numeral 2]

def transitionCodomain (n : ℕ) : SetTheorySemisentence 1 :=
  prod.dfn.nestFormulaeFunc ![
    numeral (n + 1),
    prod.dfn.nestFormulaeFunc ![numeral 2, numeral 3]]

/-- The set-theoretic graph of a two-symbol Turing machine's totalized transition function. -/
def instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : SetTheorySemisentence 1 :=
  finiteSet (transitionEntries M)

/-- Given some configuration, the next configuartion of a Turing machine (abstractified). -/
def nextConfig (n : ℕ) (instructions : SetTheorySemisentence 1) : SetTheorySemisentence 2 :=
  f“z' z.
    -- both z and z' are configurations
    z ∈ !(configSet n) ∧
    z' ∈ !(configSet n) ∧
    ∃ t, t =
      -- the new configuration has the state as instructed
      !value.dfn (!instructions)
        (!kpair.dfn (!kpair.π₁.dfn z)
          (!value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z))
            (!kpair.π₁.dfn (!kpair.π₂.dfn z)))) ∧
      !kpair.π₁.dfn z' = !kpair.π₁.dfn t ∧
      -- shift the cursor of the machine, depending on the direction
      ((!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(numeral 0)) ∧
          !integerPred.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn z'))
            (!kpair.π₁.dfn (!kpair.π₂.dfn z))) ∨
        (!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(numeral 1)) ∧
          !kpair.π₁.dfn (!kpair.π₂.dfn z') = !kpair.π₁.dfn (!kpair.π₂.dfn z)) ∨
        (!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(numeral 2)) ∧
          !integerSucc.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn z'))
            (!kpair.π₁.dfn (!kpair.π₂.dfn z)))) ∧
      -- the new value of the tape at the cursor
      !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z'))
          (!kpair.π₁.dfn (!kpair.π₂.dfn z)) =
        !kpair.π₁.dfn (!kpair.π₂.dfn t) ∧
      -- the new tape agrees with the old in all but at most one place
      ∀ k ∈ !integers,
        k ≠ !kpair.π₁.dfn (!kpair.π₂.dfn z) →
          !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z')) k =
            !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z)) k”

/-- The graph of the one-step configuration function determined by the transition table `instructions`. -/
def nextStep (n : ℕ) (instructions : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  f“p. ∀ e, e ∈ p ↔ ∃ z ∈ !(configSet n), ∃ z' ∈ !(configSet n),
    e = !kpair.dfn z z' ∧ !(nextConfig n instructions) z' z”

/-- The binary tape whose value is the blank symbol `0` at every integer position. -/
def emptyTape : SetTheorySemisentence 1 :=
  f“f. f ∈ !function.dfn (!(numeral 2)) (!integers) ∧
    ∀ i ∈ !integers, !value.dfn f i = !(numeral 0)”

/-- The initial configuration: state `0`, head position `0`, and the blank tape. -/
def initialConfig : SetTheorySemisentence 1 :=
  f“z. z = !kpair.dfn (!(numeral 0)) (!kpair.dfn (!integerZero) (!emptyTape))”

/-- The set-theoretic sentence asserting that `M` reaches its encoded halting state. -/
def halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : SetTheorySentence :=
  f“∃ m ∈ !integers, ∃ g ∈ !function.dfn (!(numeral 2)) (!integers),
    !kpair.dfn (!(numeral n)) (!kpair.dfn m g) ∈
      !orbit (!(nextStep (n + 1) (instructionTable M))) (!initialConfig)”

end BackgroundDefs

/-- The smallest natural number `n` for which the value of BB(n) can not be proven. More precisely:
the smallest `n` for which there is a Turing machine with `n` states such that ZFC can neither prove
nor disprove that the machine halts (assuming ZFC is sound).

Using the Shoenfield's absoluteness theorem, one can show that one can replace "ZFC" with "ZF"
without the value of this constant changing. -/
noncomputable def C14 : ℕ :=
  sInf {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ halts M ∧ 𝗭𝗙𝗖 ⊬ ∼halts M}

/-- Proven by Lin and Radó in [LS1965] by computing $BB(3) = 21$. -/
@[category research solved, AMS 3 68]
theorem c14_ge_4 : 4 ≤ C14 := by sorry

/-- An intermediate lower bound, proved by Brady in [B1983] by explicitly computing
$BB(4) = 107$. -/
@[category research solved, AMS 3 68]
theorem c14_ge_5 : 5 ≤ C14 := by sorry

/-- The current best known lower bound, proved by Blanchard et al. in [BB2025] by explcitily computing
$BB(5) = 47176870$. -/
@[category research solved, AMS 3 68]
theorem c14_lower_bound : 6 ≤ C14 := by sorry

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 3 68]
theorem c14_lower_bound_improved : answer(sorry) ↔ 6 < C14 := by sorry

/-- The first known upper bound, proved by Yedidia and Aaronson in [YS2016]. Their construction
reduces the independence problem to a graph-theoretic setting. -/
@[category research solved, AMS 3 68]
theorem c14_le_7910 : C14 ≤ 7910 := by sorry

/-- An intermediate upper bound, proved by O'Rear in [O2016]. It uses a Turing machine that
enumerates proofs in ZF. -/
@[category research solved, AMS 3 68]
theorem c14_le_748 : C14 ≤ 748 := by sorry

/-- The current best known upper bound, proved by Wade in [W2025]. It refines the proof-enumerating
machine construction from [O2016]. -/
@[category research solved, AMS 3 68]
theorem c14_upper_bound : C14 ≤ 432 := by sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 3 68]
theorem c14_upper_bound_improved : answer(sorry) ↔ C14 < 432 := by sorry

/-- Conjecture 11 in [A2020] by Scott Aaronson -/
@[category research open, AMS 3 68]
theorem c14_le_20 : C14 ≤ 20 := by sorry

end Constant14

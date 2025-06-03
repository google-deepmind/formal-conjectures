/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.Attributes.AMS

open Lean Elab Meta Qq

/-! # Problem Formalisation Attributes

## The Category Attribute:

### Overview
Provides information of the type of a statement. This can be:
- A mathematical problem (high school/undergraduate/graduate/research level).
  If this is a research problem then the user is also required to specify
  whether the problem has already been solved.
- An API statement
- A "test" statement

### Values
The values of this attribute are
- `@[category high_school]` : a high school level math problem.
- `@[category undergraduate]` : an undergraduate level math problem.
- `@[category graduate]` : a graduate level math problem.
- `@[category research open]` : an open reseach level math problem.
- `@[category research solved]` : a solved reseach level math problem.
  The criterion for being solved is that there exists an informal solution
  that is widely accepted by experts in the area. In particular, this
  does *not* require a formal solution to exist.
- `@[category test]` : a statement that serves as a sanity check (e.g. for a new definition).
- `@[category API]` : a statement that constructs basic theory around a new definition

### Usage examples
The tag should be used as follows:
```
@[category high_school]
theorem imo_2024_p6
    (IsAquaesulian : (ℚ → ℚ) → Prop)
    (IsAquaesulian_def : ∀ f, IsAquaesulian f ↔
      ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y) :
    IsLeast {(c : ℤ) | ∀ f, IsAquaesulian f → {(f r + f (-r)) | (r : ℚ)}.Finite ∧
      {(f r + f (-r)) | (r : ℚ)}.ncard ≤ c} 2 := by
  sorry

@[category research open]
theorem an_open_problem : Transcendental ℝ (π + rexp 1) := by
  sorry

@[category test]
theorem a_test_to_sanity_check_some_definition : ¬ FermatLastTheoremWith 1 := by
  sorry
```

## The Problem Subject Attribute

Provides information about the subject of a mathematical problem, via a
numeral corresponding to the AMS subject classification of the problem.
This can be used as follows:
```
@[AMS 11] -- 11 correponds to Number Theory in the AMS classification
theorem FLT : FermatLastTheorem := by
  sorry
```

The complete list of subjects can be found here:
https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf


In order to access the list from within a Lean file, use the `#AMS` command.

Note: the current implementation of the attribute includes all the main categories
in the AMS classification for completeness. Some are not relevant to this repository.

-/

-- TODO(lezeau): can we/should we do this using
-- `Lean.EnumAttributes` or `Lean.ParametricAttribute` ?

namespace ProblemAttributes

inductive ProblemStatus
  /-- Indicates that a mathematical problem is still open. -/
  | open
  /-- Indicates that a mathematical problem is already solved,
  i.e., there is a published (informal) proof that is widely accepted by experts. -/
  | solved
  deriving Inhabited, BEq, Hashable, ToExpr

syntax problemStatus := &"open" <|> &"solved"

/-- Convert from a syntax node to a name. -/
private def problemStatus.toName (stx : TSyntax ``problemStatus) : Option Name :=
  match stx with
    | `(problemStatus| open) => ``ProblemStatus.open
    | `(problemStatus| solved) => ``ProblemStatus.solved
    | _ => none

/-- A type to capture the various types of statements that appear in our Lean files. -/
inductive Category
  /-- A high school level math problem. -/
  | highSchool
  /-- An undegraduate level math problem. -/
  | undergraduate
  /-- A graduate level math problem. -/
  | graduate
  /-- A reseach level math problem. This can be open, or already solved -/
  | research : ProblemStatus → Category
  /-- A test statement that serves as a sanity check (e.g. for a new definition)-/
  | test
  /-- An "API" statement, i.e. a statement that constructs basic theory around a new definition -/
  | API
  deriving Inhabited, BEq, Hashable, ToExpr

syntax CategorySyntax := &"high_school" <|> &"undergraduate" <|> &"graduate"
    <|> (&"research" problemStatus) <|> &"test" <|> &"API"

-- TODO(lezeau): do we eventually want to account for the problem's source?
structure CategoryTag where
  /-- The name of the declaration with the given tag. -/
  declName : Name
  /-- The status of the problem. -/
  category : Category
  /-- The (optional) comment that comes with the given declaration. -/
  informal : String
  deriving Inhabited, BEq, Hashable, ToExpr

/-- Defines the `categoryExt` extension for adding a `HashSet` of `Tag`s
to the environment. -/
initialize categoryExt : SimplePersistentEnvExtension CategoryTag (Std.HashSet CategoryTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addCategoryEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (cat : Category) (comment : String) : m Unit :=
  modifyEnv (categoryExt.addEntry ·
    { declName := declName, category := cat, informal := comment })

structure SubjectTag where
  /-- The name of the declaration with the given tag. -/
  declName : Name
  /-- The subject(s) of the problem. -/
  subjects : List AMS
  /-- The (optional) comment that comes with the given declaration. -/
  informal : String
  deriving Inhabited, BEq, Hashable, ToExpr

/-- Defines the `tagExt` extension for adding a `HashSet` of `Tag`s
to the environment. -/
initialize subjectExt : SimplePersistentEnvExtension SubjectTag (Std.HashSet SubjectTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addSubjectEntry {m : Type → Type} [MonadEnv m] (name : Name)
    (subjects : List AMS) (informal : String) : m Unit :=
  modifyEnv (subjectExt.addEntry ·
    { declName := name, subjects := subjects, informal := informal })

/-- Convert from a syntax node to a term of type `Category` and annotate the syntax
with the corresponding name's docstring. -/
private def Syntax.toCategory (stx : TSyntax ``CategorySyntax) : CoreM Category := do
  match stx with
  | `(CategorySyntax| high_school) =>
    Elab.addConstInfo stx ``Category.highSchool
    return Category.highSchool
  | `(CategorySyntax| undergraduate) =>
    Elab.addConstInfo stx ``Category.undergraduate
    return Category.undergraduate
  | `(CategorySyntax| graduate) =>
    Elab.addConstInfo stx ``Category.graduate
    return Category.graduate
  | `(CategorySyntax| research $status) =>
    let some n := problemStatus.toName status | throwUnsupportedSyntax
    Elab.addConstInfo status n
    let status ← Lean.Meta.MetaM.run' <|
      unsafe Meta.evalExpr ProblemStatus q(ProblemStatus) (.const n [])
    Elab.addConstInfo stx ``Category.research
    return Category.research status
  | `(CategorySyntax| test) =>
    Elab.addConstInfo stx ``Category.test
    return Category.test
  | `(CategorySyntax| API) =>
    Elab.addConstInfo stx ``Category.API
    return Category.API
  | _ => throwUnsupportedSyntax

syntax (name := Category_attr) "category" CategorySyntax : attr

/-- Specifies the type of a statement.

This is used as follows: `@[category my_cat]` where `my_cat` is one of:
- `high_school` : a high school level math problem.
- `undergraduate` : an undergraduate level math problem.
- `graduate` : a graduate level math problem.
- `research open` : an open reseach level math problem.
- `research solved` : a solved reseach level math problem.
- `test` : a statement that serves as a sanity check (e.g. for a new definition).
- `API` : a statement that constructs basic theory around a new definition -/
initialize Lean.registerBuiltinAttribute {
  name := `Category_attr
  descr := "Annotation of status of a problem."
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let (status, comment) ← match stx with
      | `(attr| category $s) => withRef s do
        let cat ← Syntax.toCategory s
        return (cat, "")
      | _ => throwUnsupportedSyntax
    addCategoryEntry decl status oldDoc
  applicationTime := .beforeElaboration
}

syntax subjectList := many(num)

/-- Converts a syntax node to an array of `AMS` subjects.

This also annotates the every natural number litteral encountered, with the
description of the corresponding AMS subject (i.e. hovering over the number
in VS Code will show the subject.)
-/
def Syntax.toSubjects (stx : TSyntax ``subjectList) : MetaM (Array AMS) := do
  match stx with
  | `(subjectList|$[$nums] *) =>
    nums.mapM fun (n : TSyntax `num) => do
      let nVal := n.getNat
      let name ← numToAMSName nVal
      Elab.addConstInfo n name
      unsafe Meta.evalExpr AMS q(AMS) (.const name [])
  | _ => throwUnsupportedSyntax

syntax (name := problemSubject) "AMS" subjectList : attr

/-- Specifies the subject of a math problem.

`AMS n` indicates that a problem is related to the subject area
with index `n` in the AMS subject classification.
-/
initialize Lean.registerBuiltinAttribute {
  name := `problemSubject
  descr := "Annotation of the subject of a given problem statement"
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let subjects ← match stx with
      | `(attr| AMS $n) => withRef n <|
        Lean.Meta.MetaM.run' (Syntax.toSubjects n)
      | _ => throwUnsupportedSyntax
    addSubjectEntry decl subjects.toList oldDoc
}

section Helper

/-- Split an array into preimages of a function.

`splitByFun f arr` is the hashmap such that the value for
key `b : β` is the array of `a : α` in `arr` that get mapped
to `b` by `f` -/
private def splitByFun {α β : Type} (f : α → β) [BEq β] [Hashable β]
    (arr : Array α) : Std.HashMap β (Array α) :=
  Array.foldr addPreimage {} arr
where
  addPreimage (a : α) (m : Std.HashMap β (Array α)) :=
    m.alter (f a) (appendIfExists a)

  appendIfExists (a) : Option (Array α) → Option (Array α)
  | some arr => arr.push a
  | none => #[a]

variable {m : Type → Type} [Monad m] [MonadEnv m]

def getTags : m (Array CategoryTag) := do
  return categoryExt.getState (← MonadEnv.getEnv) |>.toArray

def getStatementTags : m (Std.HashMap Category (Array CategoryTag)) := do
  return splitByFun CategoryTag.category (← getTags)

def getCategoryStats : m (Category → Nat) := do
  let cats ← getStatementTags
  return fun c ↦ (cats.map <| fun _ arr ↦ arr.size).getD c 0

def getSubjectTags : m (Array SubjectTag) := do
  return subjectExt.getState (← MonadEnv.getEnv) |>.toArray

end Helper

end ProblemAttributes

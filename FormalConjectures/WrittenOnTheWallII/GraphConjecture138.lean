import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
A finite disproof of Graffiti.pc / Written on the Wall II, Conjecture 138.
Checked with Lean 4.33.1 and Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474.
Run `lake env lean /absolute/path/to/wowii138.lean` from that Mathlib project.
The companion manuscript proves the infinite family by hand.
-/

namespace WowII138

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open SimpleGraph Finset

/-- Adjacency at distance one or two, excluding loops. -/
def square {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
  symm := ⟨by
    rintro u v ⟨ne, edge | ⟨w, first, second⟩⟩
    · exact ⟨ne.symm, Or.inl edge.symm⟩
    · exact ⟨ne.symm, Or.inr ⟨w, second.symm, first.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (square G).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)))

/-- A witness to the existence of exactly one maximum independent set. -/
def UniqueMaximumIndependent {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ I : Finset V, G.IsIndepSet I ∧ ∀ J : Finset V, G.IsIndepSet J →
    I.card ≤ J.card → J = I

/-- The coefficient `2 + u(G)` in the catalogue. -/
def coefficient {V : Type*} (G : SimpleGraph V) (k : Nat) : Prop :=
  k = 3 ∧ UniqueMaximumIndependent G ∨ k = 2 ∧ ¬ UniqueMaximumIndependent G

/-- The catalogue bound, with both interpretations of the distance metric.
    The existence of a long induced path is encoded by a simple walk with no chords.
    For a maximum-degree set with at least two vertices, the chosen distinct pair
    realizes the minimum distance when all other eligible pairs are at least as far. -/
def Conjecture (useSquareDistance : Bool) : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    ∀ (k : Nat), coefficient G k →
    let H := square G
    let metric := if useSquareDistance then H else G
    ∀ (u v : Fin n), u ≠ v → H.degree u = H.maxDegree → H.degree v = H.maxDegree →
      (∀ (a b : Fin n), a ≠ b → H.degree a = H.maxDegree → H.degree b = H.maxDegree →
        metric.dist u v ≤ metric.dist a b) →
      ∃ (a b : Fin n) (p : G.Walk a b), p.IsPath ∧
        (∀ i j : Nat, i + 1 < j → j ≤ p.length → ¬ G.Adj (p.getVert i) (p.getVert j)) ∧
        k * metric.dist u v ≤ p.support.length

private abbrev V := Fin 19

/-- Spine 0--14, with two leaf vertices attached to each end. -/
private def edge (u v : V) : Prop :=
  u.val ≤ 14 ∧ v.val ≤ 14 ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val) ∨
  (u.val = 0 ∧ (v.val = 15 ∨ v.val = 16) ∨ v.val = 0 ∧ (u.val = 15 ∨ u.val = 16)) ∨
  (u.val = 14 ∧ 17 ≤ v.val ∨ v.val = 14 ∧ 17 ≤ u.val)

private instance : DecidableRel edge := fun u v => by unfold edge; infer_instance

private def broom : SimpleGraph V where
  Adj := edge
  symm := ⟨fun {u v} => (show ∀ u v : V, edge u v → edge v u by decide) u v⟩
  loopless := ⟨(show ∀ u : V, ¬ edge u u by decide)⟩

private instance : DecidableRel broom.Adj := fun u v => inferInstanceAs (Decidable (edge u v))

private theorem descends : ∀ v : V, v ≠ 0 → ∃ u : V, u.val < v.val ∧ broom.Adj v u := by decide

private theorem reachesZero (v : V) : broom.Reachable v 0 := by
  by_cases zero : v = 0
  · subst v; exact .refl _
  · obtain ⟨u, smaller, adjacent⟩ := descends v zero
    exact adjacent.reachable.trans (reachesZero u)
termination_by v.val

private theorem broomConnected : broom.Connected :=
  ⟨fun u v => (reachesZero u).trans (reachesZero v).symm⟩

private def chosen : Finset V := {1, 3, 5, 7, 9, 11, 13, 15, 16, 17, 18}

/-- Collapse each edge in a fixed eight-edge matching toward its chosen endpoint. -/
private def representative (v : V) : V :=
  if v = 0 then 15 else if v = 14 then 17 else
    if v.val ≤ 12 ∧ v.val % 2 = 0 then Fin.ofNat 19 (v.val - 1) else v

private theorem uniqueIndep : UniqueMaximumIndependent broom := by
  refine ⟨chosen, by decide, ?_⟩
  intro S independent large
  have collisions : ∀ u v : V,
      representative u = representative v → u ≠ v → broom.Adj u v := by decide
  have inj : Set.InjOn representative (S : Set V) := by
    intro u hu v hv same
    by_contra different
    exact independent hu hv different (collisions u v same different)
  have lands : ∀ v : V, representative v ∈ chosen := by decide
  have onto : S.image representative = chosen := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro v hv
      obtain ⟨u, _, rfl⟩ := mem_image.mp hv
      exact lands u
    · rwa [card_image_of_injOn inj]
  have pin (a : V) (member : a ∈ chosen)
      (exclude : ∀ v : V, representative v = a → v ≠ a → v ∉ S) : a ∈ S := by
    obtain ⟨v, hv, same⟩ := mem_image.mp (onto.symm ▸ member)
    by_contra absent
    have different : v ≠ a := fun h => absent (h ▸ hv)
    exact exclude v same different hv
  have singleton (a : V) (member : a ∈ chosen)
      (single : ∀ v : V, representative v = a → v = a) : a ∈ S := by
    exact pin a member fun v h ne => (ne (single v h)).elim
  have via (a b : V) (member : a ∈ chosen) (selected : b ∈ S)
      (link : ∀ v : V, representative v = a → v ≠ a → broom.Adj v b) : a ∈ S := by
    exact pin a member fun v h ne hv =>
      independent hv selected (link v h ne).ne (link v h ne)
  have at13 : (13 : V) ∈ S := singleton 13 (by decide) (by decide)
  have at16 : (16 : V) ∈ S := singleton 16 (by decide) (by decide)
  have at18 : (18 : V) ∈ S := singleton 18 (by decide) (by decide)
  have at15 : (15 : V) ∈ S := via 15 16 (by decide) at16 (by decide)
  have at17 : (17 : V) ∈ S := via 17 18 (by decide) at18 (by decide)
  have at11 : (11 : V) ∈ S := via 11 13 (by decide) at13 (by decide)
  have at9 : (9 : V) ∈ S := via 9 11 (by decide) at11 (by decide)
  have at7 : (7 : V) ∈ S := via 7 9 (by decide) at9 (by decide)
  have at5 : (5 : V) ∈ S := via 5 7 (by decide) at7 (by decide)
  have at3 : (3 : V) ∈ S := via 3 5 (by decide) at5 (by decide)
  have at1 : (1 : V) ∈ S := via 1 3 (by decide) at3 (by decide)
  have classified : ∀ v : V, v ∈ chosen →
      v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7 ∨ v = 9 ∨ v = 11 ∨ v = 13 ∨
      v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 := by decide
  have subset : chosen ⊆ S := by
    intro v hv
    rcases classified v hv with h | h | h | h | h | h | h | h | h | h | h <;>
      subst v <;> assumption
  exact (eq_of_subset_of_card_le subset (by rw [← card_image_of_injOn inj, onto])).symm

/-- Search for a path with the specified number of additional vertices. -/
private def extendPath {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nat → Fin n → List (Fin n) → Bool
  | 0, _, _ => true
  | k + 1, x, available => available.any fun y =>
      decide (G.Adj x y) && extendPath G k y (available.erase y)

private theorem extendPath_complete {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : Nat) (x : Fin n) (tail available : List (Fin n))
    (long : k ≤ tail.length) (chain : (x :: tail).IsChain G.Adj)
    (distinct : tail.Nodup) (remaining : ∀ y ∈ tail, y ∈ available) :
    extendPath G k x available = true := by
  induction k generalizing x tail available with
  | zero => rfl
  | succ k ih =>
    cases tail with
    | nil => simp at long
    | cons y ys =>
      have ⟨first, rest⟩ := List.isChain_cons_cons.mp chain
      have ⟨notRepeated, distinctTail⟩ := List.nodup_cons.mp distinct
      apply List.any_eq_true.mpr
      refine ⟨y, remaining y (by simp), ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨first, ?_⟩
      apply ih y ys (available.erase y) (by simpa using long) rest distinctTail
      intro z hz
      exact (List.mem_erase_of_ne (show z ≠ y from fun he => notRepeated (he ▸ hz))).2
        (remaining z (by simp [hz]))

private theorem noPath18 : ∀ x : V,
    extendPath broom 17 x ((List.finRange 19).erase x) = false := by decide

private theorem pathBound {x y : V} (p : broom.Walk x y) (simple : p.IsPath) :
    p.support.length ≤ 17 := by
  let tail := p.support.tail
  have support : p.support = x :: tail := by cases p <;> rfl
  by_contra! long
  have nd := simple.support_nodup
  have chain := p.isChain_adj_support
  rw [support] at nd chain long
  have ⟨noRoot, tailDistinct⟩ := List.nodup_cons.mp nd
  have reaches := extendPath_complete broom 17 x tail ((List.finRange 19).erase x)
    (by simp at long; omega) chain tailDistinct (fun z hz =>
      (List.mem_erase_of_ne (show z ≠ x from fun h => noRoot (h ▸ hz))).2 (by simp))
  rw [noPath18 x] at reaches
  contradiction

private theorem maxDegreeVertices : ∀ v : V,
    (square broom).degree v = (square broom).maxDegree ↔ v = 1 ∨ v = 13 := by decide

private def coordinate (v : V) : Nat :=
  if v.val ≤ 14 then v.val + 1 else if v.val ≤ 16 then 0 else 16

private theorem edgeStep : ∀ u v : V, broom.Adj u v → coordinate v ≤ coordinate u + 1 := by decide

private theorem squareStep : ∀ u v : V, (square broom).Adj u v →
    coordinate v ≤ coordinate u + 2 := by
  rintro u v ⟨_, edge | ⟨w, first, second⟩⟩
  · have := edgeStep u v edge; omega
  · have := edgeStep u w first
    have := edgeStep w v second
    omega

private theorem walkStepBound {G : SimpleGraph V} (step : Nat)
    (h : ∀ u v, G.Adj u v → coordinate v ≤ coordinate u + step)
    {u v : V} (p : G.Walk u v) : coordinate v ≤ coordinate u + step * p.length := by
  induction p with
  | nil => simp
  | @cons a b c edge rest ih =>
    have adjacent := h a b edge
    simp only [Walk.length_cons, Nat.mul_succ]
    omega

private theorem squareConnected : (square broom).Connected :=
  broomConnected.mono (fun _ _ h => ⟨h.ne, Or.inl h⟩)

private theorem distancesLarge : ∀ (useSquare : Bool),
    6 ≤ (if useSquare then square broom else broom).dist 1 13 := by
  intro useSquare
  cases useSquare
  · change 6 ≤ broom.dist 1 13
    obtain ⟨p, distance⟩ := broomConnected.exists_walk_length_eq_dist 1 13
    have bound := walkStepBound 1 edgeStep p
    have start : coordinate 1 = 2 := by decide
    have finish : coordinate 13 = 14 := by decide
    rw [distance, start, finish] at bound
    omega
  · change 6 ≤ (square broom).dist 1 13
    obtain ⟨p, distance⟩ := squareConnected.exists_walk_length_eq_dist 1 13
    have bound := walkStepBound 2 squareStep p
    have start : coordinate 1 = 2 := by decide
    have finish : coordinate 13 = 14 := by decide
    rw [distance, start, finish] at bound
    omega

/-- The same graph disproves the conjecture using either distance metric. -/
theorem conjecture138_false (useSquare : Bool) : ¬ Conjecture useSquare := by
  intro conjecture
  let G := if useSquare then square broom else broom
  have minimal : ∀ (a b : V), a ≠ b → (square broom).degree a = (square broom).maxDegree →
      (square broom).degree b = (square broom).maxDegree → G.dist 1 13 ≤ G.dist a b := by
    intro a b distinct first second
    rcases (maxDegreeVertices a).mp first with rfl | rfl <;>
      rcases (maxDegreeVertices b).mp second with rfl | rfl
    · exact (distinct rfl).elim
    · exact le_rfl
    · rw [G.dist_comm (u := (13 : V)) (v := (1 : V))]
    · exact (distinct rfl).elim
  have first := (maxDegreeVertices 1).mpr (Or.inl rfl)
  have second := (maxDegreeVertices 13).mpr (Or.inr rfl)
  obtain ⟨a, b, p, simple, _, lower⟩ :=
    conjecture 19 broom broomConnected 3 (Or.inl ⟨rfl, uniqueIndep⟩) 1 13 (by decide)
      first second minimal
  have upper := pathBound p simple
  have distance := distancesLarge useSquare
  omega

#print axioms conjecture138_false

end WowII138

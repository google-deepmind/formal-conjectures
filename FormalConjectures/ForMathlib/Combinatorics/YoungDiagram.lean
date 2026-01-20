open YoungDiagram

def YoungDiagram.Cell (μ : YoungDiagram) : Type := μ.cells

instance (μ : YoungDiagram) : Fintype μ.Cell :=
  inferInstanceAs (Fintype μ.cells)

instance (μ : YoungDiagram) : DecidableEq μ.Cell :=
  inferInstanceAs (DecidableEq μ.cells)

/-- The simple graph of a Young diagram: two distinct cells are
  adjacent iff they lie in the same row or in the same column. -/
def YoungDiagram.toSimpleGraph (μ : YoungDiagram) : SimpleGraph (YoungDiagram.Cell μ) :=
  SimpleGraph.fromRel fun a b =>
    (Prod.fst a.val = Prod.fst b.val) ∨ (Prod.snd a.val = Prod.snd b.val)

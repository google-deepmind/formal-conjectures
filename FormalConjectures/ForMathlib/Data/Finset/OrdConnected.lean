import Mathlib.Data.Finset.Defs
import Mathlib.Order.Interval.Set.Defs

abbrev Finset.OrdConnected {α} [Preorder α] (s : Finset α) := s.toSet.OrdConnected

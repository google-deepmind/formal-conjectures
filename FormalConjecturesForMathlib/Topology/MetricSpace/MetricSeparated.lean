import Mathlib.Topology.EMetricSpace.Defs



open EMetric Set
open scoped ENNReal

noncomputable section

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]

/-!
### Metric-separated sets

In this section we define the predicate `Metric.IsSeparated'` for `ε`-separated sets.
-/

/-- A set `s` is `≥ ε`-separated if its elements are pairwise at distance greater or equal to
 `ε` from each other. -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

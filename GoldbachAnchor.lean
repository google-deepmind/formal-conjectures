/-
GoldbachAnchor.lean — TIGHT theorem BES-3 (single anchor)
G(214) = 8 = 2^N_c at the framework anchor S = 2K.
-/
import Bes.Definitions
import Mathlib.Data.Nat.Prime.Basic

namespace Bes

/-- Goldbach pair count: pairs (p, q) with p ≤ q, p + q = n, both prime. -/
def GoldbachCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter
    (fun p => p ≤ n - p ∧ Nat.Prime p ∧ Nat.Prime (n - p))
  |>.card

/-- BES-3 (anchor): G(214) = 8 = 2^N_c.

    The 8 Goldbach pairs summing to 214 are:
    (3, 211), (17, 197), (23, 191), (41, 173),
    (47, 167), (83, 131), (101, 113), (107, 107).

    Note (107, 107) = (K, K) — the M_K-fixed pair at the framework anchor.
-/
theorem goldbach_at_S : GoldbachCount S_atlas = 8 := by
  native_decide

/-- 2^N_c = 8 holds (sanity check). -/
theorem two_pow_Nc_eq_eight : 2 ^ N_c = 8 := by
  rfl

/-- The Goldbach anchor identity: G(2K) = 2^N_c. -/
theorem goldbach_anchor : GoldbachCount (2 * K_atlas) = 2 ^ N_c := by
  show GoldbachCount 214 = 8
  native_decide

end Bes

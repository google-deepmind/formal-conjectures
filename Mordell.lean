/-
Mordell.lean — TIGHT theorem BES-11
The hard residue set H_840 equals exactly QR((Z/840)*).
-/
import Bes.Definitions

namespace Bes

/-- BES-11a: Mordell residues = squares of unit primes mod 840. -/
theorem mordell_eq_unit_squares :
    Mordell = (UnitPrimes : Finset ℕ).image (fun q => ((q * q : ℕ) : ZMod M840)) := by
  native_decide

/-- BES-11b: Mordell residues = QR((Z/840)*) (the central theorem). -/
theorem mordell_eq_QR_840 :
    Mordell = QR_840 := by
  native_decide

/-- BES-11c: |Mordell| = 6 = 1 · 1 · 2 · 3 (CRT product). -/
theorem mordell_card_eq_six : Mordell.card = 6 := by
  native_decide

/-- BES-11d: All Mordell residues are 1 mod 8. -/
theorem mordell_eq_one_mod_eight :
    ∀ r ∈ Mordell, (r.val % 8 : ℕ) = 1 := by
  native_decide

/-- BES-11e: All Mordell residues are 1 mod 3. -/
theorem mordell_eq_one_mod_three :
    ∀ r ∈ Mordell, (r.val % 3 : ℕ) = 1 := by
  native_decide

/-- BES-11f: Mordell residues mod 5 lie in {1, 4} (the QR mod 5). -/
theorem mordell_QR_mod_five :
    ∀ r ∈ Mordell, (r.val % 5 : ℕ) ∈ ({1, 4} : Finset ℕ) := by
  native_decide

/-- BES-11g: Mordell residues mod 7 lie in {1, 2, 4} (the QR mod 7). -/
theorem mordell_QR_mod_seven :
    ∀ r ∈ Mordell, (r.val % 7 : ℕ) ∈ ({1, 2, 4} : Finset ℕ) := by
  native_decide

end Bes

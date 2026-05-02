/-
Frobenius.lean — TIGHT theorem BES-13
x → x^29 mod 840 is an involution preserving Mordell and Π_Heeg as sets.
-/
import Bes.Definitions

namespace Bes

/-- Frobenius operator: x → x^29 mod 840. -/
def Phi_Gal (x : ZMod M840) : ZMod M840 := x ^ FrobExp

/-- BES-13a: Frobenius is an involution on (Z/840)*.
    Equivalently: 29² ≡ 1 mod 840 on the unit group. -/
theorem frobenius_involution_on_units :
    ∀ x : ZMod M840, Nat.gcd x.val M840 = 1 → Phi_Gal (Phi_Gal x) = x := by
  native_decide

/-- BES-13b: Frobenius preserves Mordell as a set. -/
theorem frobenius_preserves_mordell :
    Mordell.image Phi_Gal = Mordell := by
  native_decide

/-- BES-13c: Frobenius preserves Π_Heeg as a set. -/
theorem frobenius_preserves_pi_heeg :
    PiHeeg.image Phi_Gal = PiHeeg := by
  native_decide

/-- BES-13d: 1 and 169 are Frobenius fixed points in Mordell. -/
theorem mordell_fixed_points :
    Phi_Gal (1 : ZMod M840) = 1 ∧ Phi_Gal (169 : ZMod M840) = 169 := by
  native_decide

/-- BES-13e: 121 ↔ 361 form a Frobenius orbit. -/
theorem mordell_orbit_121_361 :
    Phi_Gal (121 : ZMod M840) = 361 ∧ Phi_Gal (361 : ZMod M840) = 121 := by
  native_decide

/-- BES-13f: 289 ↔ 529 form a Frobenius orbit. -/
theorem mordell_orbit_289_529 :
    Phi_Gal (289 : ZMod M840) = 529 ∧ Phi_Gal (529 : ZMod M840) = 289 := by
  native_decide

/-- BES-13g: Π_Heeg has parallel orbit structure: 671, 839 fixed; (311,551), (479,719) size-2. -/
theorem pi_heeg_orbit_structure :
    Phi_Gal (671 : ZMod M840) = 671 ∧
    Phi_Gal (839 : ZMod M840) = 839 ∧
    Phi_Gal (311 : ZMod M840) = 551 ∧
    Phi_Gal (551 : ZMod M840) = 311 ∧
    Phi_Gal (479 : ZMod M840) = 719 ∧
    Phi_Gal (719 : ZMod M840) = 479 := by
  native_decide

end Bes

import WeilReciprocalPairedTestV8

open Set Filter Topology Complex MeasureTheory
open scoped ContDiff BigOperators

set_option autoImplicit false

noncomputable section

example
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilReciprocalFnV8 f) s =
      mellin f.1 (1 - s) :=
  weil_reciprocal_mellin_v8 f s

example
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilPairedTestV8 f).1 s =
      mellin f.1 s + mellin f.1 (1 - s) :=
  weil_paired_test_mellin_v8 f s

example
    (f : WeilCompactSmoothGV1) (c t : ℝ) :
    mellin (WeilPairedTestV8 f).1
        ((c : ℂ) + (t : ℂ) * I) =
      WeilPairedMellinProfileV5 f c t :=
  weil_paired_test_fixed_line_profile_v8 f c t

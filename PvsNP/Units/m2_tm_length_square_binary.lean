import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_square_clock
import PvsNP.Units.m2_polytime_iff_time_poly
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.m2_tm_length_square_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (x.length ^ 2)) := by
  obtain ⟨c, M, hM⟩ := PvsNP.Units.m2_square_clock
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length ^ 2) true) :=
    (PvsNP.Units.m2_polytime_iff_time_poly _ _ _).2
      ⟨Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C c, M, fun n => by simpa using hM n⟩
  have h2 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 PvsNP.Units.m2_unary_to_binary_polytime
  convert h2 using 1
  funext x
  simp

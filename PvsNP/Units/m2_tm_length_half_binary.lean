import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.m2_tm_length_half_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.length / 2)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (x.length / 2) true)
    (fun x : List Bool => Nat.bits x.length)
    (PvsNP.Units.m2_tm_unary_div_const 2) PvsNP.Units.m2_unary_to_binary_polytime
  have hEq : (fun x : List Bool => Nat.bits x.length) ∘
        (fun x : List Bool => List.replicate (x.length / 2) true)
      = (fun x : List Bool => Nat.bits (x.length / 2)) := by
    funext x
    simp [Function.comp_apply]
  rw [hEq] at h
  exact h

import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_npcomplete_of_sat_reduction

theorem PvsNP.Units.m3_nphard_upward :
    ∀ Q R : List Bool → Prop, CookLevin.NPhard Q → CookLevin.reducesPoly Q R → CookLevin.NPhard R := by
  intro Q R hQ hQR L hL
  exact PvsNP.Units.m3_npcomplete_of_sat_reduction.reducesPoly_trans L Q R (hQ L hL) hQR

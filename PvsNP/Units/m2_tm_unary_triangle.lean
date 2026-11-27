import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_tm_unary_div_const

-- Built from the settled campaign units fr_ladner (mulU) and m2_tm_unary_div_const (make.fun pvsnp campaign).

namespace PvsNP.Units.m2_tm_unary_triangle

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem hMul : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => mulU x (true :: x)) :=
  cpt_mulU2 cpt_id (cpt_cons1 true cpt_id)

theorem hHalf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (x.length / 2) true) :=
  PvsNP.Units.m2_tm_unary_div_const 2

theorem hTri : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (x.length * (x.length + 1) / 2) true) := by
  have h := cpt_comp hMul hHalf
  have e : (fun a : List Bool => List.replicate ((mulU a (true :: a)).length / 2) true) =
      (fun x : List Bool => List.replicate (x.length * (x.length + 1) / 2) true) := by
    funext a
    simp [mulU, un]
  rw [e] at h
  exact h

end PvsNP.Units.m2_tm_unary_triangle

theorem PvsNP.Units.m2_tm_unary_triangle :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length * (x.length + 1) / 2) true) :=
  PvsNP.Units.m2_tm_unary_triangle.hTri

import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_flatmap
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_list_code_cons

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem main_proof :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true] ++ p.2) := by
  have hfirst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.flatMap (fun b : Bool => [b, b]) ++ [false, true]) :=
    cpt_app2 PvsNP.Units.tf_fun_flatmap (cpt_const [false, true])
  have hprod : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool =>
        (p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true], p.2)) :=
    PvsNP.Units.m2_prod_map_polytime
      (fun x : List Bool => x.flatMap (fun b : Bool => [b, b]) ++ [false, true])
      (fun x : List Bool => x)
      hfirst
      ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hcomp :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true], p.2))
      (fun p : List Bool × List Bool => p.1 ++ p.2)
      hprod
      PvsNP.Units.m2_pair_split_polytime.2.2
  have heq :
      ((fun p : List Bool × List Bool => p.1 ++ p.2) ∘
        (fun p : List Bool × List Bool =>
          (p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true], p.2))) =
      (fun p : List Bool × List Bool =>
        p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true] ++ p.2) := by
    funext p
    simp [Function.comp_apply, List.append_assoc]
  rwa [heq] at hcomp

end PvsNP.Units.m2_tm_list_code_cons

/-- Putting a string in front of a list written with doubled bits and 01 ends takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_list_code_cons :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        p.1.flatMap (fun b : Bool => [b, b]) ++ [false, true] ++ p.2) :=
  PvsNP.Units.m2_tm_list_code_cons.main_proof

import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime

namespace PvsNP.Units.m2_ww_in_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private theorem unpairB_half_cons (x : List Bool) :
    unpairB (half x ++ false :: x) = (x.take (x.length / 2), x.drop (x.length / 2)) := by
  rw [half_eq]
  simp [unpairB, un]

private abbrev wwDec (x : List Bool) : Bool :=
  decide ((unpairB (half x ++ false :: x)).1 = (unpairB (half x ++ false :: x)).2)

private theorem cpt_wwDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer wwDec := by
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hPair : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => unpairB (half x ++ false :: x)) :=
    cpt_comp hCut cpt_unpairB
  have henc : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hEq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    rw [henc]
    exact PvsNP.Units.m2_eq_polytime
  exact cpt_comp (ea := fun x : List Bool => x)
    (eb := PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair)
    (ec := Computability.encodeBool)
    (f := fun x : List Bool => unpairB (half x ++ false :: x))
    (g := fun p : List Bool × List Bool => decide (p.1 = p.2))
    hPair hEq

theorem ww_in_p_main :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool) ∈ PvsNP.P := by
  refine ⟨wwDec, cpt_wwDec, fun x => ?_⟩
  change (∃ y : List Bool, x = y ++ y) ↔ wwDec x = true
  simp only [wwDec, unpairB_half_cons, decide_eq_true_eq]
  constructor
  · rintro ⟨y, rfl⟩
    have hlen : (y ++ y).length / 2 = y.length := by
      rw [List.length_append]
      omega
    rw [hlen, List.take_left, List.drop_left]
  · intro h
    refine ⟨x.take (x.length / 2), ?_⟩
    conv_lhs => rw [← List.take_append_drop (x.length / 2) x]
    rw [h]

end PvsNP.Units.m2_ww_in_p

theorem PvsNP.Units.m2_ww_in_p :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_ww_in_p.ww_in_p_main

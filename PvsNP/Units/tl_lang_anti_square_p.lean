import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_pair_build_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

namespace PvsNP.Units.tl_lang_anti_square_p

private theorem mapNot :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map not) := by
  refine filterMap_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ (fun b => some (!b)) ?_
  intro x
  induction x with
  | nil => rfl
  | cons b x ih => exact congrArg (List.cons (!b)) ih

private def halves (x : List Bool) := unpairB (half x ++ false :: x)

private theorem halves_spec (x : List Bool) :
    halves x = (x.take (x.length / 2), x.drop (x.length / 2)) := by
  simp [halves, half_eq, unpairB, un]

theorem decider :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y.map not} : Language Bool) ∈ PvsNP.P := by
  have cut := cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have left : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (halves x).1) := by
    unfold halves
    exact cpt_comp (f := fun x => half x ++ false :: x) (g := fun s => (unpairB s).1) cut cpt_unpairB1
  have right : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (halves x).2) := by
    unfold halves
    exact cpt_comp (f := fun x => half x ++ false :: x) (g := fun s => (unpairB s).2) cut cpt_unpairB2
  have pair := PvsNP.Units.m2_pair_build_polytime _ _
    (PvsNP.Units.m2_pair_build_polytime.cpt_comp left mapNot) right
  refine ⟨_, PvsNP.Units.m2_pair_build_polytime.cpt_comp pair PvsNP.Units.m2_eq_polytime, ?_⟩
  intro x
  change (∃ y : List Bool, x = y ++ y.map not) ↔
    decide ((halves x).1.map not = (halves x).2) = true
  rw [halves_spec, decide_eq_true_eq]
  constructor
  · rintro ⟨y, rfl⟩
    have mid : (y ++ y.map not).length / 2 = y.length := by
      rw [List.length_append, List.length_map]
      omega
    simp only [mid, List.take_left, List.drop_left]
  · intro agree
    refine ⟨x.take (x.length / 2), ?_⟩
    exact (List.take_append_drop (x.length / 2) x).symm.trans
      (congrArg (fun t => x.take (x.length / 2) ++ t) agree.symm)

end PvsNP.Units.tl_lang_anti_square_p

theorem PvsNP.Units.tl_lang_anti_square_p :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y.map not} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_anti_square_p.decider

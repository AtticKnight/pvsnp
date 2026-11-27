import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_bool_combine_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_cube_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-- A counter mod 3: output one `true` every third input bit. -/
def thirdD (q : Fin 3) (_ : Bool) : Fin 3 × Option Bool :=
  if q = 2 then (0, some true) else (q + 1, none)

/-- The unary length of `u` divided by 3. -/
def third (u : List Bool) : List Bool := fstRun thirdD (fun _ => none) 0 u

theorem thirdD_run (q : Fin 3) (u : List Bool) :
    fstRun thirdD (fun _ => none) q u = un ((u.length + q.val) / 3) := by
  induction u generalizing q with
  | nil =>
    have hq : q.val < 3 := q.isLt
    have h0 : q.val / 3 = 0 := by omega
    simp [fstRun, h0]
  | cons b l ih =>
    fin_cases q
    · simp [fstRun, thirdD, ih]
    · simp [fstRun, thirdD, ih]
    · have e : (l.length + 1 + 2) / 3 = l.length / 3 + 1 := by omega
      simp [fstRun, thirdD, ih, e, un_succ]

theorem third_eq (u : List Bool) : third u = un (u.length / 3) := by
  simp [third, thirdD_run]

theorem third_length (u : List Bool) : (third u).length = u.length / 3 := by
  rw [third_eq, un_length]

theorem cpt_third :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) third :=
  fst_polyTime _ _ _ thirdD (fun _ => none) 0 (fun _ => rfl)

/-- The first third of `x`. -/
private abbrev partA (x : List Bool) : List Bool := x.take (third x).length

/-- The second third of `x`. -/
private abbrev partB (x : List Bool) : List Bool :=
  (x.drop (third x).length).take (third x).length

/-- The remainder of `x` after the first two thirds. -/
private abbrev partC (x : List Bool) : List Bool :=
  (x.drop (third x).length).drop (third x).length

/-- Decider: the three parts are all equal. -/
private abbrev cubeDec (x : List Bool) : Bool :=
  decide (partA x = partB x) && decide (partB x = partC x)

private theorem cpt_cubeDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer cubeDec := by
  have henc : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hTake0 : ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
        (fun p : List Bool × List Bool => p.2.take p.1.length) := by
    rw [henc]
    exact PvsNP.Units.m2_take_drop_length_polytime.1
  have hDrop0 : ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
        (fun p : List Bool × List Bool => p.2.drop p.1.length) := by
    rw [henc]
    exact PvsNP.Units.m2_take_drop_length_polytime.2
  have hPairThird : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x => (third x, x)) :=
    cpt_pair cpt_third cpt_id
  have hTake : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.take (third x).length) :=
    cpt_comp hPairThird hTake0
  have hDrop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.drop (third x).length) :=
    cpt_comp hPairThird hDrop0
  have hPairThirdDrop : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
        (fun x => (third x, x.drop (third x).length)) :=
    cpt_pair cpt_third hDrop
  have hTake2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => (x.drop (third x).length).take (third x).length) :=
    cpt_comp hPairThirdDrop hTake0
  have hDrop2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => (x.drop (third x).length).drop (third x).length) :=
    cpt_comp hPairThirdDrop hDrop0
  have hEq : ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
        (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    rw [henc]
    exact PvsNP.Units.m2_eq_polytime
  have hEqAB : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x => decide (partA x = partB x)) :=
    cpt_comp (cpt_pair hTake hTake2) hEq
  have hEqBC : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x => decide (partB x = partC x)) :=
    cpt_comp (cpt_pair hTake2 hDrop2) hEq
  exact PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hEqAB hEqBC

theorem cube_in_p_main :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) ∈ PvsNP.P := by
  refine ⟨cubeDec, cpt_cubeDec, fun x => ?_⟩
  change (∃ y : List Bool, x = y ++ y ++ y) ↔ cubeDec x = true
  simp only [cubeDec, partA, partB, partC, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨y, rfl⟩
    have hn : (third (y ++ y ++ y)).length = y.length := by
      rw [third_eq, un_length]
      simp [List.length_append]
      omega
    rw [hn]
    have ha : (y ++ y ++ y).take y.length = y := by
      rw [List.append_assoc]
      exact List.take_left
    have hb : ((y ++ y ++ y).drop y.length).take y.length = y := by
      rw [List.append_assoc, List.drop_left]
      exact List.take_left
    have hc : ((y ++ y ++ y).drop y.length).drop y.length = y := by
      rw [List.append_assoc, List.drop_left, List.drop_left]
    exact ⟨ha.trans hb.symm, hb.trans hc.symm⟩
  · intro h
    obtain ⟨hab, hbc⟩ := h
    have hsplit : x = partA x ++ partB x ++ partC x := by
      show x = x.take (third x).length ++ (x.drop (third x).length).take (third x).length ++
        (x.drop (third x).length).drop (third x).length
      rw [List.append_assoc, List.take_append_drop (third x).length (x.drop (third x).length),
        List.take_append_drop (third x).length x]
    refine ⟨partA x, hsplit.trans ?_⟩
    simp only [partA, partB, partC]
    rw [hab, hbc]

end PvsNP.Units.tl_lang_cube_p

theorem PvsNP.Units.tl_lang_cube_p :
    ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_cube_p.cube_in_p_main

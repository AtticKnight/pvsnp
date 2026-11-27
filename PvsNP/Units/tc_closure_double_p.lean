import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_inter

/-
The lemma unpairB_half_cons and the machine for cutting a string in half are copied from the
settled file PvsNP/Units/m2_ww_in_p.lean of github.com/makedotfun/pvsnp, which builds them on the
settled unit fr_ladner (adapted there from github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, Apache License 2.0), restated in the namespace
PvsNP.Units.tc_closure_double_p.
-/

namespace PvsNP.Units.tc_closure_double_p

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

theorem unpairB_half_cons (x : List Bool) :
    unpairB (half x ++ false :: x) = (x.take (x.length / 2), x.drop (x.length / 2)) := by
  rw [half_eq]
  simp [unpairB, un]

/-- The first half of a string, in polynomial time: cut it at its middle (`half` and `unpairB` of
the settled `fr_ladner`, as in the settled `m2_ww_in_p`), then keep the first part (settled
`m2_pair_split_polytime`). -/
theorem cpt_takeHalf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.take (x.length / 2)) := by
  have hCut : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hPair : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => unpairB (half x ++ false :: x)) :=
    cpt_comp hCut cpt_unpairB
  have henc : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
      Computability.encodingProd, Computability.encodingList]
  rw [henc] at hPair
  have h := PvsNP.Units.m2_polytime_comp (fun x : List Bool => x) PvsNP.encodePair
    PvsNP.encodeString _ (fun p : List Bool × List Bool => p.1) hPair
    PvsNP.Units.m2_pair_split_polytime.1
  have e : ((fun p : List Bool × List Bool => p.1) ∘
      (fun x : List Bool => unpairB (half x ++ false :: x))) =
      (fun x : List Bool => x.take (x.length / 2)) := by
    funext x
    simp only [Function.comp, unpairB_half_cons]
  rw [e] at h
  exact h

/-- The doubled strings of `L` are the strings of the form `y ++ y` whose first half is in `L`. -/
theorem double_eq (L : Language Bool) :
    ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool) ⊓
        ({x : List Bool | x.take (x.length / 2) ∈ L} : Language Bool) := by
  ext x
  show (∃ u ∈ L, x = u ++ u) ↔ (∃ y : List Bool, x = y ++ y) ∧ x.take (x.length / 2) ∈ L
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_⟩
    have hl : (u ++ u).length / 2 = u.length := by
      rw [List.length_append]
      omega
    rw [hl, List.take_left']
    · exact hu
    · rfl
  · rintro ⟨⟨y, rfl⟩, hy⟩
    have hl : (y ++ y).length / 2 = y.length := by
      rw [List.length_append]
      omega
    rw [hl, List.take_left' rfl] at hy
    exact ⟨y, hy, rfl⟩

end PvsNP.Units.tc_closure_double_p

/-- P is closed under doubling (TM2): `x` is a doubled string of `L` exactly when `x` is of the
form `y ++ y` (settled `m2_ww_in_p`) and its first half is in `L`, which reduces to `L` by the
first-half map (settled `m2_p_down_closed`); P is closed under intersection (settled
`m2_p_inter`). -/
theorem PvsNP.Units.tc_closure_double_p :
    ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  rw [PvsNP.Units.tc_closure_double_p.double_eq]
  refine PvsNP.Units.m2_p_inter _ _ PvsNP.Units.m2_ww_in_p ?_
  exact PvsNP.Units.m2_p_down_closed _ L
    ⟨fun x => x.take (x.length / 2), PvsNP.Units.tc_closure_double_p.cpt_takeHalf,
      fun _ => Iff.rfl⟩ hL

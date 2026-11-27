import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_interleave

set_option autoImplicit false

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

namespace PvsNP.Units.tf_fun_erase_mid

/-- Transport a polytime computation along a pointwise equality. -/
private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- Erasing one element is taking the prefix and the tail of the suffix. -/
lemma eraseIdx_eq (x : List Bool) (i : Nat) :
    x.eraseIdx i = x.take i ++ (x.drop i).tail := by
  induction x generalizing i with
  | nil => cases i <;> rfl
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show a :: t.eraseIdx j = (a :: t.take j) ++ (t.drop j).tail
      rw [List.cons_append, ih j]

theorem erase_mid_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.eraseIdx (x.length / 2)) := by
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.take (x.length / 2)) :=
    cptp (cpt_comp hCut cpt_unpairB1)
      (fun x => congrArg Prod.fst (PvsNP.Units.tf_fun_interleave.unpairB_half_cons x))
  have hV : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.drop (x.length / 2)) :=
    cptp (cpt_comp hCut cpt_unpairB2)
      (fun x => congrArg Prod.snd (PvsNP.Units.tf_fun_interleave.unpairB_half_cons x))
  have hVt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => (x.drop (x.length / 2)).tail) :=
    cpt_tail1 hV
  have hRes : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.take (x.length / 2) ++ (x.drop (x.length / 2)).tail) :=
    cpt_app2 hU hVt
  exact cptp hRes (fun x => (eraseIdx_eq x (x.length / 2)).symm)

end PvsNP.Units.tf_fun_erase_mid

theorem PvsNP.Units.tf_fun_erase_mid :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.eraseIdx (x.length / 2)) :=
  PvsNP.Units.tf_fun_erase_mid.erase_mid_polyTime

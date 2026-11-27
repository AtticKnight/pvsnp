import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its machines are those of github.com/brilliant-hq/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

namespace PvsNP.Units.m2_p_rotate_closed

/-- The transducer that keeps the first symbol only. -/
def firstD : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

theorem run_first_tail (l : List Bool) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun firstD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, firstD] using ih

theorem run_first (x : List Bool) :
    x.take 1 = PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun firstD (fun _ => none) false x := by
  rcases x with _ | ⟨b, l⟩
  · rfl
  · simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, firstD, run_first_tail]

theorem cpt_take1 :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.take 1) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ firstD (fun _ => none)
    false run_first

theorem rotate_one (x : List Bool) : x.rotate 1 = x.tail ++ x.take 1 := by
  rcases x with _ | ⟨b, l⟩
  · rfl
  · simp

/-- Rotating by one is polynomial-time: the tail, then the first symbol. -/
theorem cpt_rotate :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.rotate 1) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.tail ++ x.take 1) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2 (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1 PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id) cpt_take1
  have e : (fun x : List Bool => x.rotate 1) = (fun x : List Bool => x.tail ++ x.take 1) :=
    funext rotate_one
  rw [e]
  exact h

end PvsNP.Units.m2_p_rotate_closed

/-- P is closed under rotation by one (TM2): rotate the input, then decide. -/
theorem PvsNP.Units.m2_p_rotate_closed :
    ∀ L ∈ PvsNP.P, ({x : List Bool | x.rotate 1 ∈ L} : Language Bool) ∈ PvsNP.P := by
  rintro L ⟨d, hd, hdec⟩
  exact ⟨fun x => d (x.rotate 1), PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp PvsNP.Units.m2_p_rotate_closed.cpt_rotate hd,
    fun x => hdec (x.rotate 1)⟩

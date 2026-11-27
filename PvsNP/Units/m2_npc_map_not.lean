import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_nphard_transfer

/-- Flipping every bit of the strings of an NP-complete language keeps it NP-complete (TM2). -/
theorem PvsNP.Units.m2_npc_map_not :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPComplete ({x : List Bool | x.map not ∈ L} : Language Bool) := by
  intro L hL
  have hnot : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map not) :=
    PvsNP.Units.m2_transducer_polytime Unit
      (fun _ b => ((), some (!b)))
      (fun _ => none)
      (fun _ x => x.map not)
      (fun _ => rfl)
      (fun _ _ _ => rfl)
      ()
  have hred1 : PvsNP.KarpReducible ({x : List Bool | x.map not ∈ L} : Language Bool) L :=
    ⟨fun x => x.map not, hnot, fun _ => Iff.rfl⟩
  have hred2 : PvsNP.KarpReducible L ({x : List Bool | x.map not ∈ L} : Language Bool) := by
    refine ⟨fun x => x.map not, hnot, fun x => ?_⟩
    show x ∈ L ↔ (x.map not).map not ∈ L
    have hinvol : (x.map not).map not = x := by
      induction x with
      | nil => rfl
      | cons b t ih => cases b <;> simp [ih]
    rw [hinvol]
  exact ⟨PvsNP.Units.m2_np_down_closed _ L hred1 hL.1,
    PvsNP.Units.m2_nphard_transfer L _ hL.2 hred2⟩

import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_cons_true_time

open Turing

/-- One stack serves as both input and output: push `true` on top and halt. -/
def consTM : FinTM2 :=
  { K := Unit
    k₀ := ()
    k₁ := ()
    Γ := fun _ => Bool
    Λ := Unit
    main := ()
    σ := Unit
    initialState := ()
    m := fun _ => .push () (fun _ => true) .halt }

theorem initList_consTM (x : List Bool) :
    initList consTM x = (⟨some (), (), fun _ => x⟩ : TM2.Cfg consTM.Γ consTM.Λ consTM.σ) := by
  unfold initList
  congr 1

theorem haltList_consTM (y : List Bool) :
    haltList consTM y = (⟨none, (), fun _ => y⟩ : TM2.Cfg consTM.Γ consTM.Λ consTM.σ) := by
  unfold haltList
  congr 1

theorem consStep (x : List Bool) :
    TM2.step consTM.m (⟨some (), (), fun _ => x⟩ : TM2.Cfg consTM.Γ consTM.Λ consTM.σ) =
      some ⟨none, (), fun _ => true :: x⟩ := by
  simp only [TM2.step, consTM, TM2.stepAux]
  congr 2

def inEquiv : consTM.Γ consTM.k₀ ≃ Bool := Equiv.refl Bool

def outEquiv : consTM.Γ consTM.k₁ ≃ Bool := Equiv.refl Bool

noncomputable def cons_outputs (x : List Bool) :
    TM2OutputsInTime consTM
      (List.map inEquiv.invFun (PvsNP.encodeString x))
      (some (List.map outEquiv.invFun (PvsNP.encodeString (true :: x))))
      ((fun _ : ℕ => 1) (PvsNP.encodeString x).length) :=
  { steps := 1
    evals_in_steps := by
      have h1 : List.map inEquiv.invFun (PvsNP.encodeString x) = x := List.map_id x
      have h2 : List.map outEquiv.invFun (PvsNP.encodeString (true :: x)) = true :: x :=
        List.map_id (true :: x)
      show (flip bind (TM2.step consTM.m))^[1]
          (some (initList consTM (List.map inEquiv.invFun (PvsNP.encodeString x)))) =
        some (haltList consTM (List.map outEquiv.invFun (PvsNP.encodeString (true :: x))))
      rw [h1, h2, initList_consTM, haltList_consTM]
      exact consStep x
    steps_le_m := le_refl _ }

end PvsNP.Units.m2_cons_true_time

theorem PvsNP.Units.m2_cons_true_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun y : List Bool => true :: y),
      ∀ n : ℕ, M.time n ≤ 2 * n + 3 :=
  ⟨{ tm := PvsNP.Units.m2_cons_true_time.consTM
     inputAlphabet := PvsNP.Units.m2_cons_true_time.inEquiv
     outputAlphabet := PvsNP.Units.m2_cons_true_time.outEquiv
     time := fun _ => 1
     outputsFun := PvsNP.Units.m2_cons_true_time.cons_outputs },
   fun n => by show 1 ≤ 2 * n + 3; omega⟩

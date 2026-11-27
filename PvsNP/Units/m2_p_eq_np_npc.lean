import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

/-!
If `P = NP`, every nontrivial language in `P` is NP-complete.
Membership in `NP` is immediate from the equality. Hardness: a language `L'` in `NP` is then
also in `P`, so its decider, composed with a one-step machine that writes a fixed yes-instance
or no-instance of `L`, is a Karp reduction to `L`.
-/

set_option autoImplicit false

open Turing
open PvsNP.Units.m2_const_polytime

namespace PvsNP.Units.m2_p_eq_np_npc

/-- Pop the single input bit, reset the state, then write `y` or `z`. -/
def selectProg (y z : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.getD false)
    (.branch (fun s => s)
      (.load (fun _ => false) (pushList y.reverse))
      (.load (fun _ => false) (pushList z.reverse)))

/-- The machine that, on a one-bit input, writes `y` if the bit is true and `z` otherwise. -/
def selectTM (y z : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := selectProg y z

abbrev SCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem select_step (y z : List Bool) (b : Bool) :
    TM2.step (selectProg y z) (⟨some (), false, fun _ => [b]⟩ : SCfg) =
      some ⟨none, false, fun _ => bif b then y else z⟩ := by
  simp only [TM2.step, selectProg, TM2.stepAux]
  rw [update_unit]
  cases b <;> simp [pushList_stepAux]

theorem select_run (y z : List Bool) (b : Bool) :
    (flip bind (selectTM y z).step)^[1] (some (initList (selectTM y z) [b])) =
      some (haltList (selectTM y z) (bif b then y else z)) := by
  refine (congrArg (fun c => (flip bind (selectTM y z).step)^[1] (some c))
      (initList_eq (selectTM y z) [b])).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (selectTM y z) (bif b then y else z))).symm)
  show (flip bind (selectTM y z).step)^[1]
      (some (⟨some (), false, Function.update (fun _ => []) () [b]⟩ : SCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () (bif b then y else z)⟩ : SCfg)
  rw [update_unit, update_unit, Function.iterate_succ_apply, Function.iterate_zero_apply]
  exact select_step y z b

/-- Writing a fixed yes- or no-instance from a yes/no bit is polynomial-time computable. -/
theorem select_polyTime (y z : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeAnswer PvsNP.encodeString
      (fun b : Bool => bif b then y else z) :=
  ⟨{
    tm := selectTM y z
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := 1
    outputsFun := fun b =>
      { steps := 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (selectTM y z).step)^[1]
              (some (initList (selectTM y z) x))) (hm [b])).trans
            ((select_run y z b).trans
              (congrArg (fun x => some (haltList (selectTM y z) x))
                (hm (bif b then y else z)).symm))
        steps_le_m := by
          simp [PvsNP.encodeAnswer, Computability.encodeBool] } }⟩

/-- If `L'` is in `P` and `L` is nontrivial, then `L'` Karp-reduces to `L`. -/
theorem reduces_nontrivial {L L' : Language Bool} (hL' : L' ∈ PvsNP.P)
    (y : List Bool) (hy : y ∈ L) (z : List Bool) (hz : z ∉ L) :
    PvsNP.KarpReducible L' L := by
  obtain ⟨g, hg, hdec⟩ := hL'
  refine ⟨fun x => bif g x then y else z, ?_, ?_⟩
  · have hsel := select_polyTime y z
    have hcomp :=
      PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeAnswer PvsNP.encodeString
        g (fun b => bif b then y else z) hg hsel
    exact hcomp
  · intro x
    cases hgx : g x with
    | false =>
      simp only [hgx, Bool.cond_false]
      constructor
      · intro hx
        exact absurd ((hdec x).mp hx) (by simp [hgx])
      · intro hzin
        exact absurd hzin hz
    | true =>
      simp only [hgx, Bool.cond_true]
      constructor
      · intro _
        exact hy
      · intro _
        exact (hdec x).mpr (by simp [hgx])

end PvsNP.Units.m2_p_eq_np_npc

theorem PvsNP.Units.m2_p_eq_np_npc :
    PvsNP.P = PvsNP.NP → ∀ L ∈ PvsNP.P, (∃ y : List Bool, y ∈ L) → (∃ z : List Bool, z ∉ L) →
      PvsNP.NPComplete L := by
  intro hEq L hL ⟨y, hy⟩ ⟨z, hz⟩
  refine ⟨?_, ?_⟩
  · -- `L` is in `NP` because `P = NP`.
    rw [← hEq]
    exact hL
  · intro L' hL'
    have hL'P : L' ∈ PvsNP.P := by
      rw [hEq]
      exact hL'
    exact PvsNP.Units.m2_p_eq_np_npc.reduces_nontrivial hL'P y hy z hz

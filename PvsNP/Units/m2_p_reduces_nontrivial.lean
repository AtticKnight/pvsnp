import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_inter

set_option autoImplicit false

namespace PvsNP.Units.m2_p_reduces_nontrivial

open Turing
open PvsNP.Units.m2_p_inter.PEqualNP.Library.Machines

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | b :: tl => .push () (fun _ => b) (pushList tl)

def chooseTM (y z : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ :=
    .pop () (fun _ o => o.getD false)
      (.branch id
        (.load (fun _ => false) (pushList y.reverse))
        (pushList z.reverse))

lemma stepAux_pushList (inst : DecidableEq Unit) (r acc : List Bool) :
    @TM2.stepAux Unit (fun _ => Bool) Unit Bool inst (pushList r) false (fun _ : Unit => acc) =
      ⟨none, false, fun _ => r.reverseAux acc⟩ := by
  induction r generalizing acc with
  | nil => rfl
  | cons b tl ih =>
      simp only [pushList, TM2.stepAux, List.reverseAux_cons]
      have hupd : @Function.update Unit (fun _ => List Bool) inst (fun _ => acc) () (b :: acc) =
          (fun _ => b :: acc) := by
        funext ⟨⟩; simp [Function.update]
      rw [hupd]
      exact ih (b :: acc)

lemma choose_step (y z : List Bool) (b : Bool) :
    (chooseTM y z).step (initList (chooseTM y z) ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀))) =
      some (haltList (chooseTM y z) ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁))) := by
  have hi : initList (chooseTM y z) ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀)) =
      ⟨some (), false, fun _ => [b]⟩ := by
    simp only [initList]; congr 1
  have hh : haltList (chooseTM y z) ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁)) =
      ⟨none, false, fun _ => if b then y else z⟩ := by
    simp only [haltList]; congr 1
  rw [hi, hh]
  have hupd : @Function.update Unit (fun _ => List Bool) (chooseTM y z).decidableEqK
      (fun _ => [b]) () [] = (fun _ => []) := by
    funext ⟨⟩; simp [Function.update]
  cases b with
  | true =>
      simp only [FinTM2.step, chooseTM, TM2.step, TM2.stepAux, List.head?_cons,
        Option.getD_some, id, Bool.cond_true, List.tail_cons, ↓reduceIte]
      have hpush : @TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList y.reverse) false (fun _ : Unit => []) = ⟨none, false, fun _ => y⟩ := by
        simpa [List.reverseAux_eq_append] using stepAux_pushList (chooseTM y z).decidableEqK y.reverse []
      exact congrArg some ((congrArg (@TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList y.reverse) false) hupd).trans hpush)
  | false =>
      simp only [FinTM2.step, chooseTM, TM2.step, TM2.stepAux, List.head?_cons,
        Option.getD_some, id, Bool.cond_false, List.tail_cons, Bool.false_eq_true, ↓reduceIte]
      have hpush : @TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList z.reverse) false (fun _ : Unit => []) = ⟨none, false, fun _ => z⟩ := by
        simpa [List.reverseAux_eq_append] using stepAux_pushList (chooseTM y z).decidableEqK z.reverse []
      exact congrArg some ((congrArg (@TM2.stepAux Unit (fun _ => Bool) Unit Bool (chooseTM y z).decidableEqK
          (pushList z.reverse) false) hupd).trans hpush)

noncomputable def choosePoly (y z : List Bool) :
    TM2ComputableInPolyTime PvsNP.encodeAnswer PvsNP.encodeString
      (fun b : Bool => if b then y else z) where
  tm := chooseTM y z
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b :=
    { steps := 1
      evals_in_steps := by
        have h1 : @List.map Bool ((chooseTM y z).Γ (chooseTM y z).k₀)
            (Equiv.refl Bool).invFun (PvsNP.encodeAnswer b) =
            ([b] : List ((chooseTM y z).Γ (chooseTM y z).k₀)) := rfl
        have h2 : @List.map Bool ((chooseTM y z).Γ (chooseTM y z).k₁)
            (Equiv.refl Bool).invFun (if b then y else z) =
            ((if b then y else z) : List ((chooseTM y z).Γ (chooseTM y z).k₁)) := List.map_id _
        exact (congrArg (fun l => (flip bind (chooseTM y z).step)^[1]
            (some (initList (chooseTM y z) l))) h1).trans
          ((choose_step y z b).trans
            (congrArg (fun l => some (haltList (chooseTM y z) l)) h2.symm))
      steps_le_m := by simp }

lemma reduces_nontrivial (L₁ L₂ : Language Bool) (hL₁ : L₁ ∈ PvsNP.P)
    (hy : ∃ y : List Bool, y ∈ L₂) (hz : ∃ z : List Bool, z ∉ L₂) :
    PvsNP.KarpReducible L₁ L₂ := by
  obtain ⟨f, hf, hdec⟩ := hL₁
  obtain ⟨y, hyL⟩ := hy
  obtain ⟨z, hzL⟩ := hz
  refine ⟨fun x => if f x then y else z, cpt_comp hf ⟨choosePoly y z⟩, fun x => ?_⟩
  rw [hdec x]
  cases hfx : f x with
  | false => simp [hfx, hzL]
  | true => simp [hfx, hyL]

end PvsNP.Units.m2_p_reduces_nontrivial

theorem PvsNP.Units.m2_p_reduces_nontrivial :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → (∃ y : List Bool, y ∈ L₂) → (∃ z : List Bool, z ∉ L₂) →
      PvsNP.KarpReducible L₁ L₂ :=
  PvsNP.Units.m2_p_reduces_nontrivial.reduces_nontrivial
